#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <map>

using namespace llvm;
using namespace std;

namespace {
	const string update_func = "updateInstrInfo";
	const string print_func = "printOutInstrInfo";

	BasicBlock::iterator getLastInstr(BasicBlock *bb) {
		BasicBlock::iterator slow = bb->begin(), fast = bb->begin();
		++fast;
		while (fast != bb->end()) {
			++slow;
			++fast;
		}
		return slow;
	}

	struct CountDynamicInstr : public FunctionPass {
		static char ID;
		
		CountDynamicInstr() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			Module *module = F.getParent();
			
			/*** 1. Define External Functions ***/

			// 1.1 define update function
			vector<Type *> update_params(2, IntegerType::get(module->getContext(), 32));
			FunctionType *update_functype = FunctionType::get(
				Type::getVoidTy(module->getContext()), update_params, false);
			
			// 1.2 define print function 
			vector<Type *> print_params;
			FunctionType *print_functype = FunctionType::get(
				Type::getVoidTy(module->getContext()), print_params, false);
			
			/*** 2. Insert Call to Update and Print ***/
			for (Function::iterator i = F.begin(); i != F.end(); ++i) {
				// 2.1 count instruction in this basic block
				map<int, int> count;
				for (BasicBlock::iterator j = i->begin(); j != i->end(); ++j)
					++count[j->getOpcode()];
				
				// 2.2 call update before last instruction (in case of return)
				for (map<int, int>::iterator iter = count.begin(); iter != count.end(); ++iter) {
					Instruction *last = (Instruction *)getLastInstr((BasicBlock *)i);
					IRBuilder<> builder(last);
					Function *call = (Function *)module->getOrInsertFunction(update_func, update_functype);
					
					// create arguments for update
					vector<Value *> temp;
					temp.push_back(builder.getInt32(iter->first));
					temp.push_back(builder.getInt32(iter->second));
					ArrayRef<Value *> update_args(temp);

					builder.CreateCall(call, update_args);
				}	

				// 2.3 call print before return
				for (BasicBlock::iterator j = i->begin(); j != i->end(); ++j) {
					string opcode = string(j->getOpcodeName());
					if (opcode != "ret")
						continue;	
					IRBuilder<> builder((Instruction *)j);
					Function *call = (Function *)module->getOrInsertFunction(print_func, print_functype);
					builder.CreateCall(call);
				}
			}
			return false;
		}
	};
}

char CountDynamicInstr::ID = 0;
static RegisterPass<CountDynamicInstr> X("cse231-cdi", false, false);
