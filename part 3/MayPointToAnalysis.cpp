#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <map>
#include <set>
#include <string>
#include <vector>
#include <algorithm>

#include "231DFA.h"

using namespace llvm;
using namespace std;

namespace {
	/*
	 * derived class of 231DFA.h/Info
	 * represent information at each program point for liveness analysis
	 */
	class MayPointToInfo : public Info {
		public:
			MayPointToInfo() {}

			void print() {
				vector<pair<string, string>> data;
				for (auto iter = pointdict.begin(); iter != pointdict.end(); ++iter) {
					string ptr = iter->first;
					for (string mem : iter->second) {
						string message = ptr + "->(" + mem + "/)";
						data.push_back(make_pair(ptr, message));
					}
				}
				sort(data.begin(), data.end(), [](pair<string, string> &a, pair<string, string> &b) -> bool {
					int xa = stoi(a.first.substr(1)), xb = stoi(b.first.substr(1));
					return a.first[0] > b.first[0] || (a.first[0] == b.first[0] && xa < xb);
				});
				for (int i = 0; i < data.size(); ++i)
					errs() << data[i].second << "|";
				errs() << "\n";
			}

			static bool equal(MayPointToInfo *info1, MayPointToInfo *info2) {
				if (info1->pointdict.size() != info2->pointdict.size())
					return false;
				for (auto iter = info1->pointdict.begin(); iter != info1->pointdict.end(); ++iter) {
					string ptr = iter->first;
					if (!info2->pointdict.count(ptr) || info1->pointdict[ptr] != info2->pointdict[ptr])
						return false;
				}
				return true;
			}

			static MayPointToInfo *join(MayPointToInfo *info1, MayPointToInfo *info2, MayPointToInfo *result) {
				if (result == nullptr)
					result = new MayPointToInfo();
				if (result != info1) {
					for (auto iter = info1->pointdict.begin(); iter != info1->pointdict.end(); ++iter) {
						string ptr = iter->first;
						if (result->pointdict.count(ptr))
							result->pointdict[ptr].insert(info1->pointdict[ptr].begin(), info1->pointdict[ptr].end());
						else
							result->pointdict[ptr] = info1->pointdict[ptr];
					}
				}
				if (result != info2) {
					for (auto iter = info2->pointdict.begin(); iter != info2->pointdict.end(); ++iter) {
						string ptr = iter->first;
						if (result->pointdict.count(ptr))
							result->pointdict[ptr].insert(info2->pointdict[ptr].begin(), info2->pointdict[ptr].end());
						else
							result->pointdict[ptr] = info2->pointdict[ptr];
					}
				}
				return result;
			}

			map<string, set<string>> pointdict;
	};

	/*
	 * derived class of 231DFA.h/DataFlowAnalysis
	 */
	template<class Info, bool Direction>
	class MayPointToAnalysis: public DataFlowAnalysis<Info, Direction> {
		public:
			MayPointToAnalysis(Info &bottom, Info &initialState):
				DataFlowAnalysis<Info, Direction>::DataFlowAnalysis(bottom, initialState) {
			}

			~MayPointToAnalysis() {}

		private:
			virtual void flowfunction(Instruction *I, vector<unsigned> &IncomingEdges, vector<unsigned> &OutgoingEdges, vector<Info *> &Infos) {
				if (I == nullptr)
					return;
				unsigned index = this->InstrToIndex[I];
				string op = I->getOpcodeName();

				// join incoming information
				Info *temp = new Info();
				for (unsigned src : IncomingEdges) {
					pair<unsigned, unsigned> e = make_pair(src, index);
					temp = Info::join(this->EdgeToInfo[e], temp, temp);
				}

				// case 1: alloca		OUT = IN + {Ri -> Mi}
				if (op == "alloca") {
					string ptr = "R" + to_string(index), mem = "M" + to_string(index);	
					temp->pointdict[ptr].insert(mem);
				}
				
				// case 2: bitcast		OUT = IN + {Ri -> X | Rv -> X in IN}
				else if (op == "bitcast") {
					string ptr = "R" + to_string(index);
					Instruction *var = (Instruction *)I->getOperand(0);
					if (this->InstrToIndex.count(var)) {
						unsigned v = this->InstrToIndex[var];
						string rv = "R" + to_string(v);
						temp->pointdict[ptr].insert(temp->pointdict[rv].begin(), temp->pointdict[rv].end());
					}
				}
				
				// case 3: getelementptr	OUT = IN + {Ri -> X | Rv -> X in IN}
				else if (op == "getelementptr") {
					string ptr = "R" + to_string(index);
					Instruction *var = (Instruction *)I->getOperand(0);
					if (this->InstrToIndex.count(var)) {
						unsigned v = this->InstrToIndex[var];
						string rv = "R" + to_string(v);
						temp->pointdict[ptr].insert(temp->pointdict[rv].begin(), temp->pointdict[rv].end());
					}
				}

				// case 4: load			OUT = IN + {Ri -> Y | Rp -> X in IN and X -> Y in IN}
				else if (op == "load") {
					if (I->getType()->isPointerTy()) {
						string ptr = "R" + to_string(index);
						Instruction *var = (Instruction *)I->getOperand(0);
						if (this->InstrToIndex.count(var)) {
							unsigned p = this->InstrToIndex[var];
							string rp = "R" + to_string(p);
							set<string> mems;
							for (string x : temp->pointdict[rp])
								mems.insert(temp->pointdict[x].begin(), temp->pointdict[x].end());
							temp->pointdict[ptr].insert(mems.begin(), mems.end());
						}
					}
				}

				// case 5: store		OUT = IN + {Y -> X | Rv - >X in IN and Rp -> Y in IN}
				else if (op == "store") {
					Instruction *var0 = (Instruction *)I->getOperand(0), *var1 = (Instruction *)I->getOperand(1);
					if (this->InstrToIndex.count(var0) && this->InstrToIndex.count(var1)) {
						unsigned v = this->InstrToIndex[var0], p = this->InstrToIndex[var1];
						string rv = "R" + to_string(v), rp = "R" + to_string(p);
						set<string> mems;
						for (string x : temp->pointdict[rv])
							mems.insert(x);
						for (string y : temp->pointdict[rp])
							temp->pointdict[y].insert(mems.begin(), mems.end());
					}
				}

				// case 6: select		OUT = IN + {Ri -> X | R1 -> X in IN} + {Ri -> X | R2 -> X in IN}
				else if (op == "select") {
					string ptr = "R" + to_string(index);
					Instruction *var1 = (Instruction *)I->getOperand(1), *var2 = (Instruction *)I->getOperand(2);
					set<string> mems;
					if (this->InstrToIndex.count(var1)) {
						string r1 = "R" + to_string(this->InstrToIndex[var1]);
						mems.insert(temp->pointdict[r1].begin(), temp->pointdict[r1].end());
					}
					if (this->InstrToIndex.count(var2)) {
						string r2 = "R" + to_string(this->InstrToIndex[var2]);
						mems.insert(temp->pointdict[r2].begin(), temp->pointdict[r2].end());
					}
					temp->pointdict[ptr].insert(mems.begin(), mems.end());
				}
			
				// case 7: phi			OUT = IN + {Ri -> X | Rk -> X in IN, k = 1, 2, ..., K}
				else if (op == "phi") {
					int start = index, end = index;
					while (true) {
						++end;
						if (this->IndexToInstr.find(end) == this->IndexToInstr.end() ||
								this->IndexToInstr[end] == nullptr ||
								string(this->IndexToInstr[end]->getOpcodeName()) != "phi")
							break;
					}
					
					for (int idx = start; idx < end; ++idx) {
						string ptr = "R" + to_string(index);
						set<string> mems;
						unsigned num = I->getNumOperands();
						for (int k = 0; k < num; ++k) {
							Instruction *vark = (Instruction *)I->getOperand(k);
							if (this->InstrToIndex.count(vark)) {
								string rk = "R" + to_string(this->InstrToIndex[vark]);
								mems.insert(temp->pointdict[rk].begin(), temp->pointdict[rk].end());
							}
						}
						temp->pointdict[ptr].insert(mems.begin(), mems.end());
					}
				}

				// case 8: others		OUT = IN
				else {
					;
				}

				for (int i = 0; i < Infos.size(); ++i)
					Info::join(Infos[i], temp, Infos[i]);
				delete temp;
			}	
	};

	/*
	 * a function pass do the reaching defintion analysis
	 */
	struct MayPointToAnalysisPass : public FunctionPass {
		static char ID;

		MayPointToAnalysisPass() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			MayPointToInfo bottom;
			MayPointToAnalysis <MayPointToInfo, true> mpa(bottom, bottom);
			mpa.runWorklistAlgorithm(&F);
			mpa.print();
			return false;
		}

	};
};

char MayPointToAnalysisPass::ID = 0;
static RegisterPass<MayPointToAnalysisPass> X("cse231-maypointto", false, false);
