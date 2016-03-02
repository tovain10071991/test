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

static map<Instruction*, Module*> indirectBranch_moduleCopy_set;
static map<Instruction*, Instruction*> indirectBranch_instCopy_set;

bool is_indirect_branch(Instruction* inst);
Instruction* map_inst_copy(Function* func, unsigned inst_no);		//返回func中第inst_no条指令
void update_function(Function* func, Instruction* inst);

int main(int argc, char **argv)
{

	OwningPtr<MemoryBuffer> buf;
	MemoryBuffer::getFile(Twine(argv[1]), buf);
	if(!buf)
		errx(-1, "get file failed.");

	LLVMContext& context = getGlobalContext();
	Module* mdl = ParseBitcodeFile(&*buf, context);
	if(!mdl)
		errx(-1, "parse bitcode file failed.");

	//先分析main函数
	Function* func = mdl->getFunction("main");

	unsigned inst_no = 0;	//作为函数中指令的编号，从1起为第一条指令。编号用于判断那个间接分支是已经分析过的

	//遍历指令，查找间接分支(先只找间接call)，并clone module
	for(auto inst_iter = inst_begin(func); inst_iter != inst_end(func); ++inst_iter)
	{
		++inst_no;
		//判断是不是间接call,是就clone module
		if(is_indirect_branch(&*inst_iter))
		{
			Module* module_copy = CloneModule(mdl);
			indirectBranch_moduleCopy_set[&*inst_iter] = module_copy;
			indirectBranch_instCopy_set[&*inst_iter] = map_inst_copy(module_copy->getFunction("main"), inst_no);
		}
	}
	//删减module
	for(auto indirectBranch_moduleCopy_iter = indirectBranch_moduleCopy_set.begin(); indirectBranch_moduleCopy_iter != indirectBranch_moduleCopy_set.end(); ++indirectBranch_moduleCopy_iter)
	{
		inst_no = 0;
		Module* module_copy = indirectBranch_moduleCopy_iter->second;
		Instruction* inst_copy = indirectBranch_instCopy_set[indirectBranch_moduleCopy_iter->first];
		Function* func_copy = module_copy->getFunction("main");

		update_function(func_copy, inst_copy);
	}

	return 0;
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

Instruction* map_inst_copy(Function* func, unsigned inst_no)		//返回func中第inst_no条指令
{
	unsigned inst_no_tmp = 0;
	for(auto inst_iter = inst_begin(func); inst_iter != inst_end(func); ++inst_iter)
	{
		++inst_no_tmp;
		if(inst_no_tmp == inst_no)
			return &*inst_iter;
	}
	errx(-1, "fail in map_inst_copy");
	return NULL;
}

void update_succ_bb(BasicBlock* bb);

void update_function(Function* func, Instruction* inst)
{
	cerr << "================" << endl;
	inst->dump();
	cerr << "================" << endl;
	set<Value*> associate_value_set;
	//先把inst的opr放入关联集，移除inst本身
	for(unsigned i = 0, num_opr = inst->getNumOperands(); i < num_opr; ++i)
	{
		if(isa<Constant>(inst->getOperand(i))||isa<BasicBlock>(inst->getOperand(i)))
			continue;
		cerr << "add associate: " << endl;
		inst->getOperand(i)->dump();
		associate_value_set.insert(inst->getOperand(i));
	}
	
	//将inst本身标记为要移除，...，最后将要移除的指令移到unreach_bb
	bool update_associate = false;
	set<Instruction*> notMove_set;	//在该set中表示为已分析过且不移除(除了第一个加入的间接分支)，不在该set中则表示需要分析
	notMove_set.insert(inst);
	do{
		update_associate = false;
		for(auto inst_iter = inst_begin(func); inst_iter != inst_end(func); ++inst_iter)
		{
			if(notMove_set.find(&*inst_iter)!=notMove_set.end())	//在set中表示已分析过
				continue;
			//判断指令本身或opr是否在关联集，是就将该指令标记为不可删，且用指令本身和指令的opr更新关联集
			if(associate_value_set.find(&*inst_iter)==associate_value_set.end())	//如果该指令本身不在关联集，就判断其操作数在不在关联集
			{
				for(unsigned i = 0, num_opr = inst_iter->getNumOperands(); i < num_opr; ++i)
				{
					if(associate_value_set.find(inst_iter->getOperand(i))!=associate_value_set.end())
						goto next;
				}
				continue;		//如果指令本身不在关联集且opr也都不在关联集，则遍历下一条指令
			}
next:		//到了这里，说明指令本身或opr在关联集，将指令本身和opr加进关联集
			cerr << "meet inst: " << endl;
			inst_iter->dump();
			notMove_set.insert(&*inst_iter);
			if(associate_value_set.insert(&*inst_iter).second)
			{
				cerr << "add inst into associate: " << endl;
				inst_iter->dump();
				update_associate = true;
			}
			for(unsigned i = 0, num_opr = inst_iter->getNumOperands(); i < num_opr; ++i)
			{
				if(isa<Constant>(inst_iter->getOperand(i))||isa<BasicBlock>(inst_iter->getOperand(i)))
					continue;
				if(associate_value_set.insert(inst_iter->getOperand(i)).second)
				{
					cerr << "add inst's opr into associate: " << endl;
					inst_iter->getOperand(i)->dump();
					update_associate = true;
				}
			}
		}
	}while(update_associate);

	//移除指令前，先保存CFG
	map<BasicBlock*, set<BasicBlock*> > bb_predBbSet_set;
	map<BasicBlock*, set<BasicBlock*> > bb_succBbSet_set;
	for(auto bb_iter = func->begin(); bb_iter != func->end(); ++bb_iter)
	{
		for(auto pred_bb_iter = pred_begin(&*bb_iter); pred_bb_iter != pred_end(&*bb_iter); ++pred_bb_iter)
			bb_predBbSet_set[&*bb_iter].insert(*pred_bb_iter);
		for(auto succ_bb_iter = succ_begin(&*bb_iter); succ_bb_iter != succ_end(&*bb_iter); ++succ_bb_iter)
			bb_succBbSet_set[&*bb_iter].insert(*succ_bb_iter);
	}
	
	//移除标记完毕，现在开始移除。创建unreach_bb，把要移除的指令放到这里
	BasicBlock* unreach_bb = BasicBlock::Create(getGlobalContext(), "unreach_bb", func);
	IRBuilder<> builder(getGlobalContext());
	builder.SetInsertPoint(unreach_bb);
	builder.CreateRetVoid();
	Instruction* unreach_term = unreach_bb->getTerminator();
	inst->moveBefore(unreach_term);
	
	Instruction* will_move_inst = 0;
	for(auto inst_iter = inst_begin(func); inst_iter != inst_end(func); ++inst_iter)
	{
		if(inst_iter->getParent()==unreach_bb)
			continue;
		if(will_move_inst)
		{
			cerr << "will move: " << endl;
			will_move_inst->dump();
			will_move_inst->moveBefore(unreach_term);
			will_move_inst = 0;
		}
		if(notMove_set.find(&*inst_iter)==notMove_set.end())
		{
			will_move_inst = &*inst_iter;
		}
	}
	if(will_move_inst)
	{
		cerr << "will move: " << endl;
		will_move_inst->dump();
		will_move_inst->moveBefore(unreach_term);
		will_move_inst = 0;
	}

	cerr << "==============" << endl;
	func->dump();

	//删除多余bb(即内容是空的)
	for(auto bb_iter = func->begin(); bb_iter != func->end(); ++bb_iter)
	{
		bb_iter->dump();
		if(!bb_iter->empty())
			update_succ_bb(&*bb_iter, bb_predBbSet_set, bb_succBbSet_set);
/*		if(bb_iter->empty())
		{
			cerr << "is's empty" << endl;
			//将该bb的后继bb置为前驱bb的后继bb，并从前驱bb中删除该bb
			for(auto pred_bb_iter = bb_predBbSet_set[&*bb_iter].begin(); pred_bb_iter != bb_predBbSet_set[&*bb_iter].end(); ++pred_bb_iter)
			{
				bb_succBbSet_set[*pred_bb_iter].erase(&*bb_iter);
				for(auto succ_bb_iter = bb_succBbSet_set[&*bb_iter].begin(); succ_bb_iter != bb_succBbSet_set[&*bb_iter].end(); ++succ_bb_iter)
				{
					bb_succBbSet_set[*pred_bb_iter].insert(*succ_bb_iter);
				}
			}
		}
*/	}
	cerr << "#############" << endl;
	for(auto bb_iter = func->begin(); bb_iter != func->end(); ++bb_iter)
	{
		cerr << "=======" << endl;
		bb_iter->dump();
		cerr << "pred bb: " << endl;
		for(auto pred_bb_iter = bb_predBbSet_set[&*bb_iter].begin(); pred_bb_iter != bb_predBbSet_set[&*bb_iter].end(); ++pred_bb_iter)
		{
			(*pred_bb_iter)->dump();
		}
		cerr << "succ bb: " << endl;
		for(auto succ_bb_iter = bb_succBbSet_set[&*bb_iter].begin(); succ_bb_iter != bb_succBbSet_set[&*bb_iter].end(); ++succ_bb_iter)
		{
			(*succ_bb_iter)->dump();
		}
	}
}

void update_succ_bb(BasicBlock* bb, map<BasicBlock*, set<BasicBlock*> > bb_predBbSet_set, map<BasicBlock*, set<BasicBlock*> > bb_succBbSet_set)
{
	//遍历后继基本块，如果不是空的，就把该后继bb前驱bb的后继bb集中；如果后继bb是空的，就把后继bb的后继放到前驱bb的后继bb集中
