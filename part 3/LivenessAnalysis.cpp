#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <map>
#include <set>
#include <string>

#include "231DFA.h"

using namespace llvm;
using namespace std;

namespace {
	/*
	 * derived class of 231DFA.h/Info
	 * represent information at each program point for liveness analysis
	 */
	class LivenessInfo : public Info {
		public:
			LivenessInfo() {}

			void print() {
				for (auto life : lives)
					errs() << life << "|";
				errs() << "\n";
			}

			static bool equal(LivenessInfo *info1, LivenessInfo *info2) {
				return info1->lives == info2->lives;
			}

			static LivenessInfo *join(LivenessInfo *info1, LivenessInfo *info2, LivenessInfo *result) {
				if (result == nullptr)
					result = new LivenessInfo();
				if (result != info1)
					for (auto life : info1->lives)
						result->lives.insert(life);
				if (result != info2)
					for (auto life : info2->lives)
						result->lives.insert(life);
				return result;
			}
		
		set<unsigned> lives;

	};

	/*
	 * derived class of 231DFA.h/DataFlowAnalysis
	 */
	template<class Info, bool Direction>
	class LivenessAnalysis: public DataFlowAnalysis<Info, Direction> {
		public:
			LivenessAnalysis(Info &bottom, Info &initialState):
				DataFlowAnalysis<Info, Direction>::DataFlowAnalysis(bottom, initialState) {
				for (auto iter = this->IndexToInstr.begin(); iter != this->IndexToInstr.end(); ++iter)
					errs() << iter->first << " " << iter->second->getOpcodeName() << "\n";
			}

			~LivenessAnalysis() {
				this->EdgeToInfo.clear();	
			}

		private:
			void addOperandsInfo(Instruction *I, Info *info) {
				unsigned num = I->getNumOperands();
				for (int i = 0; i < num; ++i) {
					Instruction *operand = (Instruction *)I->getOperand(i);
					if (this->InstrToIndex.find(operand) != this->InstrToIndex.end())
						info->lives.insert(this->InstrToIndex[operand]);
				}
			}

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
				
				// case 1: binary operator
				if (op == "add" || op == "fadd" || op == "sub" || op == "fsub" || op == "mul" || op == "fmul" ||
					op == "udiv" || op == "sdiv" || op == "fdiv" || op == "urem" || op == "srem" || op == "frem") {
					temp->lives.erase(index);
					addOperandsInfo(I, temp);
				}
			
				// case 2: binary bitwise operator
				else if (op == "shl" || op == "lshr" || op == "ashr" || op == "and" || op == "or" || op == "xor") {	
					temp->lives.erase(index);
					addOperandsInfo(I, temp);
				}

				// case 3: compare
				else if (op == "icmp" || op == "fcmp") {
					temp->lives.erase(index);
					addOperandsInfo(I, temp);
				}
				
				// case 4: other instructions with result
				else if (op == "alloca" || op == "load" || op == "getelementptr" || op == "select") {
					temp->lives.erase(index);
					addOperandsInfo(I, temp);
				}
				
				// case 5: phi instruction
				else if (op == "phi") {
					// 5.1 find the range of "phi" instructions
					int start = index, end = index;
					while (true) {
						++end;
						if (this->IndexToInstr.find(end) == this->IndexToInstr.end() ||
								this->IndexToInstr[end] == nullptr ||
								string(this->IndexToInstr[end]->getOpcodeName()) != "phi")
							break;
					}
					
					// 5.2 remove all "def" variables
					for (int idx = start; idx < end; ++idx) {
						temp->lives.erase(idx);
						for (int j = 0; j < Infos.size(); ++j)
							Infos[j]->lives.erase(idx);
					}
					
					// 5.3 add "use" variables only for corresponding path
					for (int idx = start; idx < end; ++idx) {
						Instruction *J = this->IndexToInstr[idx];
						unsigned num = J->getNumOperands();
						for (int j = 0; j < Infos.size(); ++j) {
							int output = OutgoingEdges[j];
							// for each output, only add variable coming from it
							for (int i = 0; i < num; ++i) {
								Instruction *var = (Instruction *)J->getOperand(i);
								if (this->IndexToInstr.find(output) != this->IndexToInstr.end() && 
										this->IndexToInstr[output] != nullptr &&
										this->InstrToIndex.find(var) != this->InstrToIndex.end() &&
										this->IndexToInstr[output]->getParent() == var->getParent()) { // same label
									Infos[j]->lives.insert(this->InstrToIndex[var]);
								}
							}
						}
					}
				}

				// case 6: instructions without result
				else
					addOperandsInfo(I, temp);

				for (int i = 0; i < Infos.size(); ++i)
					Infos[i]->lives.insert(temp->lives.begin(), temp->lives.end());
				delete temp;
			}	
	};

	/*
	 * a function pass do the reaching defintion analysis
	 */
	struct LivenessAnalysisPass : public FunctionPass {
		static char ID;

		LivenessAnalysisPass() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			LivenessInfo bottom;
			LivenessAnalysis<LivenessInfo, false> la(bottom, bottom);
			la.runWorklistAlgorithm(&F);
			la.print();
			return false;
		}

	};
};

char LivenessAnalysisPass::ID = 0;
static RegisterPass<LivenessAnalysisPass> X("cse231-liveness", false, false);
