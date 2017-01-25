#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include <map>

using namespace llvm;
using namespace std;

namespace {
	struct CountStaticInstr : public FunctionPass {
		static char ID;

		CountStaticInstr() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			map<string, int> count;
			for (Function::iterator i = F.begin(); i != F.end(); ++i)
				for (BasicBlock::iterator j = i->begin(); j != i->end(); ++j)
					++count[string(j->getOpcodeName())];
			for (map<string, int>::iterator iter = count.begin(); iter != count.end(); ++iter)
				errs() << iter->first << "\t" << iter->second << "\n";
			return false;
		}
	};
}

char CountStaticInstr::ID = 0;
static RegisterPass<CountStaticInstr> X("cse231-csi", false, false);
