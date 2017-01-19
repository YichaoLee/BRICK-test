#include "DebugInfo.h"

void DebugInfo::print(){
	errs()<<"MainFunc: "<<mainFunc<<"\n";
//	errs()<<"#Num_input: "<<counter_inputvar<<"\n";
//	errs()<<"#Num_var: "<<counter_var<<"\n";
	errs()<<"#CallDepth: "<<callLevel<<"\n";
	errs()<<"#Loc: "<<loc<<"\n";
/*
	errs()<<"#nonlinearOp: "<<counter_op<<" \n";
	for(auto &kv:nonlinearOp){
		errs()<<"\t#"<<get_m_Operator_str(kv.first)<<": "<<kv.second<<"\n";
	}
*/
}

void DebugInfo::initOpMap(){
	nonlinearOp[TAN]=0;
	nonlinearOp[ATAN]=0;
	nonlinearOp[ATAN2]=0;
	nonlinearOp[SIN]=0;
	nonlinearOp[ASIN]=0;
	nonlinearOp[COS]=0;
	nonlinearOp[ACOS]=0;
	nonlinearOp[SQRT]=0;
	nonlinearOp[POW]=0;
	nonlinearOp[LOG]=0;
	nonlinearOp[LOG10]=0;
	nonlinearOp[ABS]=0;
	nonlinearOp[EXP]=0;
	nonlinearOp[SINH]=0;
	nonlinearOp[COSH]=0;
	nonlinearOp[TANH]=0;
}

bool DebugInfo::isNonlinearOp(Op_m op){
	if(op==TAN||op==ATAN||op==ATAN2||op==SIN||op==ASIN||op==COS||op==ACOS
		||op==SQRT||op==POW||op==LOG||op==LOG10||op==ABS||op==EXP||op==SINH
		||op==COSH||op==TANH){
		return true;
	}
	else 
		return false;
}

void DebugInfo::getInstInfo(const Instruction *I){
	if(isa<CallInst>(I)){
		const CallInst *CI = dyn_cast<CallInst>(I);
		Function *F = CI->getCalledFunction();
		if(!F->isDeclaration()){
			curLevel++;
			if(curLevel>callLevel)
				callLevel = curLevel;
		}
	}
}

void DebugInfo::getFuncInfo(Function *F){
	if(F->getName()==mainFunc){
		counter_inputvar += F->arg_size();
	}
	else
		funcCnt++;
	BasicBlock::iterator it = F->getEntryBlock().begin();
	BasicBlock::iterator end = F->getEntryBlock().end();
	it++;
	Instruction *I = dyn_cast<Instruction>(it);
	unsigned beginLine,endLine;
	while(I->getDebugLoc().isUnknown()&&it!=end){
		it++;
		I = dyn_cast<Instruction>(it);
	}

	if (MDNode *N = I->getMetadata("dbg")) {  
        DILocation Loc(N);//DILocation is in DebugInfo.h  
        beginLine = Loc.getLineNumber(); 
    }
    I = F->back().getTerminator();
    if (MDNode *N = I->getMetadata("dbg")) {  
        DILocation Loc(N);//DILocation is in DebugInfo.h  
        endLine = Loc.getLineNumber();  
    }
    loc+=(endLine - beginLine+1);
}



void DebugInfo::getConsInfo(Constraint *con){
	Op_m op=con->rpvList.op;
	if(op==ALLOCA)
		counter_var++;
	else if(isNonlinearOp(op))
		counter_op++;
		
}
