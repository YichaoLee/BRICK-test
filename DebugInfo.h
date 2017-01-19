#ifndef _DEBUGINFO_h
#define _DEBUGINFO_h
#include <iostream>
#include <string>
#include <fstream>
#include <map>
#include <stdlib.h>
#include "CFG.h"
#include "convinent.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"

using namespace std;
using namespace llvm;

class DebugInfo{

public:
	string mainFunc;
	unsigned counter_inputvar;
	unsigned counter_var;
	unsigned loc;
	unsigned callLevel;
	unsigned curLevel;
	unsigned funcCnt;
	unsigned counter_op;
	map<Op_m, unsigned> nonlinearOp;
	DebugInfo(){
		counter_inputvar=0;
		counter_var=0;
		loc=0;
		callLevel=0;
		curLevel=0;
		funcCnt=0;
		counter_op=0;
		initOpMap();
	}
	DebugInfo(string funcName){
		mainFunc = funcName;
		counter_inputvar=0;
		counter_var=0;
		loc=0;
		callLevel=0;
		curLevel=0;
		funcCnt=0;
		counter_op=0;
		initOpMap();
	}

	void initOpMap();
	bool isNonlinearOp(Op_m op);
	void getInstInfo(const Instruction *I);
	void getFuncInfo(Function *F);
	void getConsInfo(Constraint *con);
	void print();

};

#endif
