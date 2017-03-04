#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <set>
#include <string>

#include "231DFA.h"

using namespace llvm;
using namespace std;

namespace {
	/*
	 * derived class of 231DFA.h/Info
	 * represent information at each program point for reaching defintion analysis
	 */
	class ReachingInfo : public Info {
		public:
			ReachingInfo() {}
			
			// print the content of defs
			void print() {
				// errs() << this << ": ";
				for (auto def : defs)
					errs() << def << "|";
				errs() << "\n";
			}
			
			// compare the defs of two ReachingInfo
			static bool equal(ReachingInfo *info1, ReachingInfo *info2) {
				return info1->defs == info2->defs;
			}
			
			// union the defs of two ReachingInfo
			static ReachingInfo *join(ReachingInfo *info1, ReachingInfo *info2, ReachingInfo *result) {
				if (result == nullptr)
					result = new ReachingInfo();
				if (result != info1)
					for (unsigned def : info1->defs)
						result->defs.insert(def);
				if (result != info2)
					for (unsigned def : info2->defs)
						result->defs.insert(def);
				return result;
			}

			set<unsigned> defs;
	};

	/*
	 * derived class of 231DFA.h/DataFlowAnalysis
	 */
	template<class Info, bool Direction>
	class ReachingDefinitionAnalysis : public DataFlowAnalysis<Info, Direction> {
		public:
			ReachingDefinitionAnalysis(Info &bottom, Info &initialState):
				DataFlowAnalysis<Info, Direction>::DataFlowAnalysis(bottom, initialState) {}
			
			~ReachingDefinitionAnalysis() {
				this->EdgeToInfo.clear();
			}

		private:
			virtual void flowfunction(Instruction *I, vector<unsigned> &IncomingEdges, vector<unsigned> &OutgoingEdges, vector<Info *> &Infos) {
				if (I == nullptr)
					return;
				unsigned index = this->InstrToIndex[I];
				string op = I->getOpcodeName();
				
				Info *temp = new Info();
				for (unsigned src : IncomingEdges) {
					pair<unsigned, unsigned> e = make_pair(src, index);
					temp = Info::join(this->EdgeToInfo[e], temp, temp);
				}

				// case 1: binary operator
				if (op == "add" || op == "fadd" || op == "sub" || op == "fsub" || op == "mul" || op == "fmul" ||
					op == "udiv" || op == "sdiv" || op == "fdiv" || op == "urem" || op == "srem" || op == "frem") {
					temp->defs.insert(index);
				}

				// case 2: binary bitwise operator
				if (op == "shl" || op == "lshr" || op == "ashr" || op == "and" || op == "or" || op == "xor") {
					temp->defs.insert(index);
				}

				// case 3: compare
				if (op == "icmp" || op == "fcmp") {
					temp->defs.insert(index);
				}
				
				// case 3: memroy-related
				if (op == "alloca" || op == "load" || op == "getelementptr" || op == "select") {
					temp->defs.insert(index);
				}

				// case 4: phi instruction
				if (op == "phi") {
					while (true) {
						temp->defs.insert(index);
						++index;
						if (this->IndexToInstr.find(index) == this->IndexToInstr.end())
							break;
						Instruction *J = this->IndexToInstr[index];
						if (string(J->getOpcodeName()) != "phi")
							break;
					}
				}

				// case 5: no result
				if (op == "br" || op == "switch" || op == "store");

				for (int i = 0; i < Infos.size(); ++i)
					Infos[i]->defs = temp->defs;
				delete temp;
			}
	};
	
	/*
	 * a function pass do the reaching defintion analysis
	 */
	struct ReachingDefinitionAnalysisPass : public FunctionPass {
		static char ID;

		ReachingDefinitionAnalysisPass() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			ReachingInfo bottom;			
			ReachingDefinitionAnalysis<ReachingInfo, true> rda(bottom, bottom);
			rda.runWorklistAlgorithm(&F);
			rda.print();
			return false;
		}

	};
};

char ReachingDefinitionAnalysisPass::ID = 0;
static RegisterPass<ReachingDefinitionAnalysisPass> X("cse231-reaching", false, false);
