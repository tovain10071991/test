// ./myproject /home/user/Documents/test/test/main.bc
#include <err.h>
#include <iostream>
#include <set>
#include <vector>

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
//	unsigned inst_num;

//	map<unsigned, Module*> indirect_branch_to_module_set;
//	map<unsigned, set<Value*> > indirect_branch_to_associate_value_set_set;
	//统计下指令数并初始化not_delete
//	for(auto inst_iter = inst_begin(func); inst_iter != inst_end(func); ++inst_iter)
//	{
//		++inst_num;
//	}
//	vector<bool> not_move(inst_num+1, false);

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
	
	//将inst本身标记为要移除，删减指令，最后将要移除的指令移到unreach_bb
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

}

/*

		if(inst_iter->getOpcode() == Instruction::Call)
		{
			if(CallInst* call_inst = dyn_cast<CallInst>(&*inst_iter))
			{
				if(call_inst->getCalledFunction()==NULL)
				{
					//indirect_branch_module_set[no_inst] = CloneModule(mdl);
					Module* mdl_copy = CloneModule(mdl);
					//在module copy中找到这条间接分支
					unsigned no_inst_copy = 0;
					set<Value*> associate_val_set;
					vector<bool> not_delete_copy(not_delete);
					Function* func_copy = mdl_copy->getFunction("main");
					for(auto inst_copy_iter = inst_begin(func_copy); inst_copy_iter != inst_end(func_copy); ++inst_copy_iter)
					{
						++no_inst_copy;
						if(no_inst_copy!=no_inst)
							continue;
						//找到module copy中的间接分支了，现在收集关联value然后删减指令吧
						if(CallInst* call_inst_copy = dyn_cast<CallInst>(&*inst_copy_iter))
						{
							associate_val_set.insert(call_inst_copy->getCalledValue());
//							call_inst_copy->getCalledValue()->dump();
							not_delete_copy[no_inst_copy] = true;
							bool update_associate;
							do{
								update_associate = false;
								no_inst_copy = 0;
								for(auto inst_tmp_iter = inst_begin(func_copy); inst_tmp_iter != inst_end(func_copy); ++inst_tmp_iter)
								{
									++no_inst_copy;
									if(not_delete_copy[no_inst_copy])	//为true表示不删表示已分析过
										continue;
									//判断指令本身或opr是否在关联集，是就将该指令标记为不可删，且用指令本身和指令的opr更新关联集
									if(associate_val_set.find(&*inst_tmp_iter)==associate_val_set.end())	//如果该指令本身不在关联集，就判断其操作数在不在关联集
									{
										for(unsigned i = 0, num_opr = inst_tmp_iter->getNumOperands(); i < num_opr; ++i)
										{
											if(associate_val_set.find(inst_tmp_iter->getOperand(i))!=associate_val_set.end())
											goto next;
										}
										continue;	//如果指令本身不在关联集且opr也都不在关联集，则遍历下一条指令
									}
next:								//到了这里，说明指令本身或opr在关联集，将指令本身和opr加进关联集
									cerr << "meet inst: " << endl;
									inst_tmp_iter->dump();
									not_delete_copy[no_inst_copy] = true;
									if(associate_val_set.insert(&*inst_tmp_iter).second)
									{
										cerr << "add inst into associate: " << endl;
										inst_tmp_iter->dump();
										update_associate = true;
									}
									for(unsigned i = 0, num_opr = inst_tmp_iter->getNumOperands(); i < num_opr; ++i)
									{
										if(isa<Constant>(inst_tmp_iter->getOperand(i))||isa<BasicBlock>(inst_tmp_iter->getOperand(i)))
											continue;
										if(associate_val_set.insert(inst_tmp_iter->getOperand(i)).second)
										{
											cerr << "add inst's opr into associate: " << endl;
											inst_tmp_iter->getOperand(i)->dump();
											update_associate = true;
										}
									}
								}
							}while(update_associate);
							//到了这里，说明module copy已经删减标记完毕，现在是真的删减了
							no_inst_copy = 0;
							Instruction* will_del_inst = 0;
							for(auto inst_tmp_iter = inst_begin(func_copy); inst_tmp_iter != inst_end(func_copy); ++inst_tmp_iter)
							{
								if(will_del_inst)
								{
									cerr << "will delete: " << endl;
									will_del_inst->dump();
									will_del_inst->removeFromParent();
									will_del_inst = 0;
								}
								++no_inst_copy;
								if(!not_delete_copy[no_inst_copy])
								{
									will_del_inst = &*inst_tmp_iter;
								}
							}
							cerr << "=====" << endl;
							func_copy->dump();
						}
						else
							errx(-1, "Really?\n");

					}
				}
			}
			else
				errx(-1, "Really?\n");
		}
*/
