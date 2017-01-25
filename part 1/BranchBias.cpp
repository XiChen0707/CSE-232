#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <string>

using namespace llvm;
using namespace std;

namespace {
	const string update_func = "updateBranchInfo";
	const string print_func = "printOutBranchInfo";

	struct BranchBias : public FunctionPass {
		static char ID;
		
		BranchBias() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			Module *module = F.getParent();
			
			/*** 1. Define External Functions ***/
			
			// 1.1 define update function
			vector<Type *> update_params;
			update_params.push_back(IntegerType::get(module->getContext(), 1));
			FunctionType *update_functype = FunctionType::get(
				Type::getVoidTy(module->getContext()), update_params, false);

			// 1.2 define print function
			vector<Type *> print_params;
			FunctionType *print_functype = FunctionType::get(
				Type::getVoidTy(module->getContext()), print_params, false);

			/*** 2. Insert Call to Update and Print ***/
			for (Function::iterator i = F.begin(); i != F.end(); ++i) {
				for (BasicBlock::iterator j = i->begin(); j != i->end(); ++j) {
					string opcode = j->getOpcodeName();
					
					// 2.1 call update before conditional branch
					if (opcode == "br" && j->getNumOperands() > 1) {
						IRBuilder<> builder((Instruction *)j);
						Function *call = (Function *)module->getOrInsertFunction(update_func, update_functype);
						vector<Value *> temp;
						temp.push_back(j->getOperand(0));
						ArrayRef<Value *> update_args(temp);
						builder.CreateCall(call, update_args);
					}

					// 2.2 call print before return
					else if (opcode == "ret") {
						IRBuilder<> builder((Instruction *)j);
						Function *call = (Function *)module->getOrInsertFunction(print_func, print_functype);
						builder.CreateCall(call);
					}
				}
			}
			return false;
		}
	};
}

char BranchBias::ID = 0;
static RegisterPass<BranchBias> X("cse231-bb", false, false);
