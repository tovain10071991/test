// ./myproject /home/user/Documents/test/test/main.bc
#include <err.h>
#include <iostream>
#include <set>
#include <vector>
#include <map>

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/system_error.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/OwningPtr.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/CFG.h"
#include "llvm/IR/IRBuilder.h"

using namespace std;
using namespace llvm;

enum ValueType {
	Unknown;
	Constant;
	Variant;
};

enum RelationType {
	Equal;
	Unequal;
	Point;
	Pointed;
};

class EqualInfo {
	ValueType val_type;
	Value* val;
	Value* point;
};

class PointInfo {
	ValueType val_type;
	Value* val;
};

map<Function*, map<Value*, EqualInfo> > func_var_equal_set;
map<Function*, map<Value*, PointInfo> > func_var_point_set;

map<Function*, set<Instruction*> > func_indirectBranchSet_set;

OwningPtr<MemoryBuffer> buf;
Module* mdl;
LLVMContext& context = getGlobalContext();

void insert_indirect_branch(Instruction* inst, Function* func)
{
	func_indirectBranchSet_set[func].insert(inst);
}

Instruction* get_first_indirect_branch(Function* func)
{
	if((auto iter = func_indirectBranchSet_set[func].begin())!=func_indirectBranchSet_set[func].end())
		return *iter;
	else
		return NULL;
}

Instruction* get_next_indirect_branch(Function* func, Instruction* indirect_branch)
{
	if((auto iter = func_indirectBranchSet_set[func].find(indirect_branch))!=func_indirectBranchSet_set[func].end())
	{
		if((++iter)!=func_indirectBranchSet_set[func].end())
			return *iter;
		else
			return NULL;
	}
	else
	{
		errx(-1, "fail in get_next_indirect_branch");
		return NULL;
	}
	return NULL;
}

void collect_indirect_branch(Function* func);
void analysis_bb(Instruction* indirect_branch);

int main(int argc, char **argv)
{

	MemoryBuffer::getFile(Twine(argv[1]), buf);
	if(!buf)
		errx(-1, "get file failed.");

	mdl = ParseBitcodeFile(&*buf, context);
	if(!mdl)
		errx(-1, "parse bitcode file failed.");

	//先分析main函数
	Function* func = mdl->getFunction("main");

	//查找函数子中的间接分支
	collect_indirect_branch(func);

	//从间接分支所在的bb开始，向上分析bb
	for(Instruction indirect_branch = get_first_indirect_branch(func); indirect_branch!=NULL; indirect_branch = get_next_indirect_branch(func, indirect_branch))
	analysis_bb(indirect_branch);

	return 0;
}

bool is_indirect_branch(Instruction* inst);

void collect_indirect_branch(Function* func)
{
	for(auto inst_iter = inst_begin(func); inst_iter != inst_end(func); ++inst_iter)
	{
		if(is_indirect_branch(&*inst_iter))
		{
			insert_indirect_branch(&*inst_iter, func);
		}
	}
	cerr << "============indirect branch============" << endl;
	for(auto iter = module_func_indirectBranchSet_set[mdl][func].begin(); iter != module_func_indirectBranchSet_set[mdl][func].end(); ++iter)
	{
		(*iter)->dump();
	}
	cerr << "=======================================" << endl;
}

bool is_indirect_call(Instruction* inst);

bool is_indirect_branch(Instruction* inst)
{
	if(is_indirect_call(inst))
		return true;
	else
		return false;
}

bool is_indirect_call(Instruction* inst)
{
	if(inst->getOpcode() == Instruction::Call)
	{
		if(CallInst* call_inst = dyn_cast<CallInst>(inst))
		{
			if(call_inst->getCalledFunction()==NULL)
				return true;
			else
				return false;
		}
		else
			errx(-1, "Really?\n");
			return false;
	}
	else
		return false;
}

void analysis_bb(Instruction* indirect_branch)
{
}
