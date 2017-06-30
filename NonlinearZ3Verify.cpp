#include "NonlinearZ3Verify.h"
#include "time.h"
#include "float.h"
using namespace std;
int Nonlinear_VERBOSE_LEVEL = 0;
int Nonlinear_UC_LEVEL=0;

//add constraint to empty vector  0==0

const int BitPerByte = 8;

/***************************table of variables in linear constraints*********************************/
    NonlinearZ3VarTable::NonlinearZ3VarTable(z3::context &ctx, CFG *ha){

        cfg = ha;
        unsigned inputID=0;
        var_num = 0;
        alloca_num = 0;
//        for(int i=0; i<cfg->mainInput.size();i++)
//            errs()<<"NonlinearZ3VarTable initial "<<cfg->mainInput[i]<<"\t"<<cfg->variableList[cfg->mainInput[i]].name<<"\n";
        for(unsigned i=0;i<cfg->variableList.size();i++)
        {
            Variable var =  cfg->variableList[i];
            VarType type = var.type;
            unsigned numBits = var.numbits;

            if(inputID<cfg->mainInput.size()&&cfg->mainInput[inputID]==i){

                if(type==FP){
                	z3::expr temp = ctx.real_const(var.name.c_str());
                    x.push_back(temp);
                }
                else if(type==INT){
	             	z3::expr temp = ctx.int_const(var.name.c_str());
                    x.push_back(temp);
                }
                exprMap[i] = var_num;
                inputID++;
                var_num++;
            }
            else if(type==FP){
                z3::expr temp = ctx.real_const(var.name.c_str());
                x.push_back(temp);
                exprMap[i] = var_num; 
                var_num++;
            }
            else if(type==INT){
                z3::expr temp = ctx.int_const(var.name.c_str());
                x.push_back(temp);
                exprMap[i] = var_num; 
                var_num++;
            }
        }
    }

    NonlinearZ3VarTable::~NonlinearZ3VarTable(){varVal.clear();alias.clear();storeMap.clear();exprMap.clear();x.clear();cfg=NULL;}

    void NonlinearZ3VarTable::setX(int ID, int time, VarType type, unsigned numBits, z3::context &ctx){

        int ID2 = exprMap[ID];
        string newName = cfg->variableList[ID].name+"/t"+int2string(time);
        if(type==FP){
            x[ID2] = ctx.real_const(newName.c_str());           
        }
        else if(type==INT){
            x[ID2] = ctx.int_const(newName.c_str());
        }
        else
            assert(false && "SetX error!!!");
    }

    int NonlinearZ3VarTable::alloca(){
        storeMap[++alloca_num] = -2;
        return alloca_num;
    }

    void NonlinearZ3VarTable::setAlias(int ID1, int ID2){
        int count = alias.count(ID2);
        if(count)
            ID2 = alias[ID2];
        alias[ID1] = ID2;
    }

    void NonlinearZ3VarTable::setAlias(Variable *v1, Variable *v2){
        int ID1=v1->ID;
        int ID2=v2->ID;
        int count = alias.count(ID2);
        if(count)
            ID2 = alias[ID2];
        alias[ID1] = ID2;
    }

    void NonlinearZ3VarTable::setVal(int ID, double val){
        varVal[ID] = val;
    }

    void NonlinearZ3VarTable::store(int ID1, int ID2){
        storeMap[ID1] = ID2;
    }

    int NonlinearZ3VarTable::getNum(){
        return var_num;    
    }
    
    z3::expr NonlinearZ3VarTable::getX(int ID){
        int count = alias.count(ID);
        if(count)
            ID = alias[ID];
        int ID2 = exprMap[ID];
        return x[ID2];
    }

    void NonlinearZ3VarTable::setX(int ID, z3::expr expr){
        int count = alias.count(ID);
        if(count)
            ID = alias[ID];
        int ID2 = exprMap[ID];
        x[ID2] = expr;
    }

    int NonlinearZ3VarTable::load(int ID){
        int count = storeMap.count(ID);
        int storeID;
        if(count){
            storeID = storeMap[ID];
            if(storeID==-2){
                errs()<<"GetLoad error1 "<<ID<<"\t"<<cfg->variableList[ID]<<"\n";
                assert(false);
            }
            return storeID;
        }
        else{
            //errs()<<"GetLoad error2 "<<ID<<"\t"<<cfg->variableList[ID]<<"\n";
            return -1;
        }
    }
    bool NonlinearZ3VarTable::hasAlias(Variable *v){
        int ID = v->ID;
        int count = alias.count(ID);
        if(count)
            return true;
        else
            return false;
    }

    Variable* NonlinearZ3VarTable::getAlias(int ID){
        int count = alias.count(ID);
        int aliasID;
        if(count){
            aliasID = alias[ID];
        }
        else{
            aliasID = ID;
        }
        return &cfg->variableList[aliasID];
    }

    Variable* NonlinearZ3VarTable::getAlias(Variable* var){
        if(var->type==INTNUM||var->type==FPNUM)
            return var;
        int ID = var->ID;
        int count = alias.count(ID);
        int aliasID;
        if(count){
            aliasID = alias[ID];
        }
        else{
            aliasID = ID;
        }
        return &cfg->variableList[aliasID];
    }

    bool NonlinearZ3VarTable::getVal(Variable *var, double &v){
        if(var->type==INTNUM||var->type==FPNUM){
            v=var->getVal();
            return true;
        }
        int ID = var->ID;
        int count = varVal.count(ID);
        if(count){
            v = varVal[ID];
            return true;
        }
        else{
            return false;
        }
    }

    bool NonlinearZ3VarTable::getVal(int ID, double &v){
        int count = varVal.count(ID);
        if(count){
            v = varVal[ID];
            return true;
        }
        else{
            return false;
        }
    }
    void NonlinearZ3VarTable::printAliasMap(){
        errs()<<"AliasMap:\n";
        for(map<int,int>::iterator it=alias.begin();it!=alias.end();++it){
            errs()<<cfg->variableList[it->first]<<"\t\t"<<cfg->variableList[it->second]<<"\n";
        }
    }
    map<int, double> NonlinearZ3VarTable::getValmap(){
           return varVal;
    }

    map<int, int> NonlinearZ3VarTable::getAliasmap(){
           return alias;
    }

    CFG *NonlinearZ3VarTable::getCFG(){
        return cfg;
    }

/********************************class NonlinearZ3Verify***********************************/
/*******************************solution of linear problems by z3**********************************/
NonlinearZ3Verify::NonlinearZ3Verify(){
	solverTime=0;
}

NonlinearZ3Verify::NonlinearZ3Verify(DebugInfo *d, int mode){
    solverTime=0;
    this->dbg = d;
    this->outMode = mode;
}

NonlinearZ3Verify::~NonlinearZ3Verify(){
    dbg = NULL;
    clear();
}


void NonlinearZ3Verify::printVector(vector<int> &path){
    for(vector<int>::iterator it=path.begin();it<path.end();it++)
        errs()<<*it<<";";
    errs()<<"\n";
}

/* verify the feasibility of the path return true:sat false:unsat  */

bool NonlinearZ3Verify::check(CFG* ha, vector<int> &path){
    clear();
    if(outMode==1){
        printPath(ha, path);
    }
    try{
        // //ha->print();
        clock_t start,finish;

        z3::expr_vector problem = encode_path(ha, path);
        // cerr<<problem<<endl;
        start = clock();

        // SubsetSolver csolver(c, problem, false);
        // MapSolver msolver(csolver.size());
        // bool res = analyze_unsat_core(csolver, msolver);
        bool res = analyze_nonlinear(problem);

        finish=clock();

        solverTime = 1000*(double)(finish-start)/CLOCKS_PER_SEC;
        
        if(!res){
            if(outMode==1)
                cerr<<"z3_result is sat\n\n\n";
            return true;
        }
    }
    catch (z3::exception ex) {
        cerr << "Error: " << ex << "\n";
        throw_error("fatal error: z3 exception");
    }
    if(outMode==1)
        cerr<<"z3_result is unsat\n\n\n";
    return false;
}

void NonlinearZ3Verify::print_sol(CFG *cfg){

}
/*
z3::expr NonlinearZ3Verify::mk_INT_cmp(z3::expr y, z3::expr z, Op_m pvop){
    z3::expr cmp(c);
    if(!z3::eq(y.get_sort(), z.get_sort())){
        y = to_real(y);
        z = to_real(z);
    }
    switch(pvop){
        case lt:cmp = (y<z);break;
        case le:cmp = (y<=z);break;
        case gt:cmp = (y>z);break;
        case ge:cmp = (y>=z);break;
        case eq:cmp = (y==z);break;
        case ne:cmp = (y!=z);break;
        default:assert(false);
    }
    z3::expr assign(c); 
    assign = ite(cmp, c.int_val(1), c.int_val(0));
    
    return assign;
}
*/
int NonlinearZ3Verify::getCMP(double rl, double rr, Op_m pvop){
    bool cmp=false;
    switch(pvop){
        case slt:cmp = ((int)rl<(int)rr);break;
        case sle:cmp = ((int)rl<=(int)rr);break;
        case sgt:cmp = ((int)rl>(int)rr);break;
        case sge:cmp = ((int)rl>=(int)rr);break;
        case ult:cmp = ((unsigned)rl<(unsigned)rr);break;
        case ule:cmp = ((unsigned)rl<=(unsigned)rr);break;
        case ugt:cmp = ((unsigned)rl>(unsigned)rr);break;
        case uge:cmp = ((unsigned)rl>=(unsigned)rr);break;
        case eq:cmp = ((int)rl==(int)rr);break;
        case ne:cmp = ((int)rl!=(int)rr);break;
        case feq:cmp = (rl==rr);break;
        case fne:cmp = (rl!=rr);break;
        case flt:cmp = (rl<rr);break;
        case fle:cmp = (rl<=rr);break;
        case fgt:cmp = (rl>rr);break;
        case fge:cmp = (rl>=rr);break;
        default:assert(false);
    }
    if(cmp)
        return 1;
    return 0;
}

char const* NonlinearZ3Verify::getRealVal(string str){
    int plusID = str.find("e+");
    if(plusID!=-1){
        plusID++;
        return str.erase(plusID, 1).c_str();
    }
    return str.c_str();
}

z3::expr NonlinearZ3Verify::getCMPExpr(Variable *v, NonlinearZ3VarTable *table){
	z3::expr Expr(c);
	if(v->type==FPNUM){
        Expr = c.real_val(getRealVal(v->name));
    }
	else if(v->type==INTNUM){
        Expr = c.int_val(getRealVal(v->name));
    }
    else
        Expr = table->getX(v->ID);
    return Expr;
}

z3::expr NonlinearZ3Verify::bvcal(z3::expr a, z3::expr b, Op_m op){
	

	check_context(a, b);
	assert(a.is_int() && b.is_int());
	Z3_ast ra = Z3_mk_int2bv(a.ctx(), 32, a);
	Z3_ast rb = Z3_mk_int2bv(b.ctx(), 32, b);
	cerr<<a<<"\t"<<z3::expr(a.ctx(), ra)<<"\n";
	cerr<<"111\n";
	cerr<<b<<"\t"<<z3::expr(a.ctx(), rb)<<"\n";
	Z3_ast z;

	switch(op){
		case AND:
			z = Z3_mk_bvand(a.ctx(), ra, rb);
			break;
		case NAND:
			z = Z3_mk_bvnand(a.ctx(), ra, rb);
			break;
		case OR:
			z = Z3_mk_bvor(a.ctx(), ra, rb);
			break;
		case XOR:
			z = Z3_mk_bvxor(a.ctx(), ra, rb);
			break;
		case SREM:
			z = Z3_mk_bvsrem(a.ctx(), ra, rb);
			break;
		case ASHR:
			z = Z3_mk_bvashr(a.ctx(), ra, rb);
			break;
		case SHL:
			z = Z3_mk_bvshl(a.ctx(), ra, rb);
			break;
		default:assert(false);
	}

	Z3_ast rz = Z3_mk_bv2int(a.ctx(), z, Z3_TRUE);
	cerr<<z3::expr(a.ctx(), rz)<<"\n";
	a.check_error();
	return z3::expr(a.ctx(), rz);

}

z3::expr NonlinearZ3Verify::getExpr(Variable *v, bool &treat, double &val, NonlinearZ3VarTable *table){

    z3::expr Expr(c);
    unsigned numBits = v->numbits;

    if(v->type==FPNUM){
    	val = v->getVal();
        string valstr = double2string(val);
        Expr = c.real_val(valstr.c_str());
    }
    else if(v->type==INTNUM){
        val = v->getVal();
        Expr = c.int_val(v->name.c_str());
    }
    else if(v->type == INT || v->type==FP){
        Expr = table->getX(v->ID);
        treat = treat&table->getVal(v->ID, val);
    }
    else
        assert(false && "GetExpr error : v->type error!!");
    return Expr;
}


// generate the z3_ast of compare constraint()
z3::expr NonlinearZ3Verify::mk_compare_ast(Constraint *con, NonlinearZ3VarTable *table){
	z3::expr exprl(c); 
    z3::expr exprr(c);
    z3::expr ast(c); 
    Operator op = con->op;

    ParaVariable lpv = con->lpvList;
    ParaVariable rpv = con->rpvList;

    assert(!lpv.isExp && "Mk_compare_ast error: lpv isExp!!!");
    assert(!rpv.isExp && "Mk_compare_ast error: rpv isExp!!!");


    Variable *lv = table->getAlias(lpv.rvar);
    Variable *rv = table->getAlias(rpv.rvar);

    assert(lv->numbits==rv->numbits && "Mk_compare_ast error: Numbits is different!!");

    int ID1 = lv->ID;
    int ID2 = rv->ID;
            
    double lval,rval;
    if(lv->type == PTR){
    	assert((op==EQ||op==NE) && "Mk_compare_ast with ptr type error!!");
        if(!table->getVal(ID1,lval)){
            // errs()<<"GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
        	assert(false && "Mk_compare_ast lval getVal error!!");
        }
        if(!table->getVal(ID2,rval)){
            // errs()<<"1.LT GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
        	assert(false && "Mk_compare_ast rval getVal error!!");
        }
        exprl = c.int_val((int)lval);
        exprr = c.int_val((int)rval);
    }
    else{
    	bool treat = false;
        exprl = getExpr(lv, treat, lval, table);
		exprr = getExpr(rv, treat, rval, table);
    }

    switch(op){
    	case EQ:case FEQ:    ast = (exprl==exprr);break;
        case NE:case FNE:    ast = (exprl!=exprr);break;
        case SLT:case ULT:case FLT:   ast = (exprl<exprr);break;
        case SLE:case ULE:case FLE:   ast = (exprl<=exprr);break;
        case SGT:case UGT:case FGT:   ast = (exprl>exprr);break;
        case SGE:case UGE:case FGE:   ast = (exprl>=exprr);break;
    	default:	assert(false && "Operator type error!!");break;
    }

    return ast;
}

z3::expr NonlinearZ3Verify::mk_eq_ast(z3::expr a, z3::expr b){
	check_context(a, b);
	Z3_ast r;
	if(a.get_sort().is_bv())
	    r = Z3_mk_eq(a.ctx(), a, b);
	else
		r = Z3_mk_fpa_eq(a.ctx(), a, b);
    a.check_error();
    return z3::to_expr(a.ctx(), r);
}

z3::expr NonlinearZ3Verify::mk_assignment_ast(Constraint *con, NonlinearZ3VarTable *table, int time){
    
    z3::expr ast(c); 
    // z3::expr exprl(c); 
    z3::expr exprr(c);

    ParaVariable lpv = con->lpvList;
    ParaVariable rpv = con->rpvList;

    assert(!lpv.isExp && "Mk_assignment_ast error: lpv is exp!!");
            
    Variable *lv = table->getAlias(lpv.rvar);

    if(lv->type==PTR){
    	if(!rpv.isExp){
            Variable *rv = table->getAlias(rpv.rvar);
            assert(rv->type==PTR && "Mk_assignment_ast PTR error: Type of rv is not PTR!!");
            table->setAlias(lv, rv);
        }
        else
        	ast = mk_ptr_operation_expr(lv, rpv, table, time);
    }
    else{
    	if(!rpv.isExp){

    		// if(time>0)
      //           table->setX(lv->ID, time, lv->type, lv->numbits, c);
      //       exprl = table->getX(lv->ID);

    		Variable *rv = table->getAlias(rpv.rvar);

    		if(rv->type==INTNUM||rv->type==FPNUM){

    			bool treat = true;
    			double val = 0;
    			exprr = getExpr(rv, treat, val, table);

    			table->setVal(lv->ID, val);
                table->setX(lv->ID, exprr);
                // ast = mk_eq_ast(exprl, exprr);
    		}
    		else{
    			
                // exprr = table->getX(rv->ID);
                table->setAlias(lv->ID, rv->ID);
                double val = 0;

                if(table->getVal(rv->ID, val))
                    table->setVal(lv->ID, val);
    		}
    	}
    	else{

    		// if(time>0)
      //           table->setX(lv->ID, time, lv->type, lv->numbits, c);
      //       exprl = table->getX(lv->ID);

	    	Op_m pvop = rpv.op;
	    	switch(pvop){
	    		case LOAD:{

	    			bool treat = true;
	    			double val=0;
	    			Variable *rvr = table->getAlias(rpv.rvar);
                    if(!table->getVal(rvr->ID, val)){
                        // errs()<<"2.LOAD GetVal error "<<rvr->ID<<"\t"<<cfg->variableList[rvr->ID].name<<"\n"; 
                        assert(false && "Mk_assignment_ast LOAD error!!");
                    }
                    int rl = (int)val;
                    int rr = table->load(rl);
                    treat = table->getVal(rr, val);
                    if(treat)
                        table->setVal(lv->ID, val);
                    
                    table->setAlias(lv->ID, rr);
                    
                    // exprr = table->getX(rr);
                    // ast = mk_eq_ast(exprl, exprr);

                    break;
	    		}
	    		case TRUNC:case ZEXT:case SEXT:case FPTRUNC:case FPEXT:case FPTOUI:case FPTOSI:case UITOFP:case SITOFP:{
	    			ast = mk_convert_expr(lv, rpv, table, time);	    		
	    			break;
	    		}
	    		case FADD:case ADD:case SUB:case FSUB:case MUL:case FMUL:case UDIV:case SDIV:case FDIV:
    			case UREM:case SREM:case FREM:
    			case LSHR:case ASHR:case SHL:case AND:case NAND:case OR:case XOR:{
    				ast = mk_binaryop_expr(lv, rpv, table, time);
    				break;
    			}
    			case ABS:case FABS:case POW:case SQRT:
                case COPYSIGN:case FMAX:case FMIN:case FDIM:{
    				ast = mk_function_expr(lv, rpv, table, time);
    				break;
    			}
                case ISNAN:case ISINF:case ISNORMAL:case ISFINITE:case SIGNBIT:case CLASSIFY:{
                    errs()<<"PVOP: "<<pvop<<"\n";
                    assert(false && "Mk_assignment_ast error: Can't handle floating-point with Nonlinear constraints!!");
                    break;
                }
    			case eq:case ne:
    			case slt:case sle:case sgt:case sge:
    			case ult:case ule:case ugt:case uge:
    			case feq:case fne:
    			case flt:case fle:case fgt:case fge:{
    				ast = mk_compare_expr(lv, rpv, table, time);
    				break;
    			}
    			default:
    				assert(false && "Mk_assignment_ast LOAD error: Op_m is not a linear operator!!");
    				break;
	    	}
    	}
    }
    
    return ast;
}

z3::expr NonlinearZ3Verify::mk_ptr_operation_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time){
	Op_m pvop = rpv.op;
	z3::expr Expr(c);
    switch(pvop){
    	case ALLOCA:{
    		//	a = alloca
    		//	PTR 	exprid
    		//	a 		allocaID(initial as -2)
    		int allocaID = table->alloca();
            table->setVal(lv->ID, allocaID);
            break;
        }
        case LOAD:{
        	//	a = Load b
        	//	PTR 	exprid
    		//	b 		allocaID
    		///////////////////////////////
    		//	expr 	alias
        	//	a 		allocaID
        	Variable *rv = table->getAlias(rpv.rvar);
    		double val = 0;
            if(!table->getVal(rv->ID, val)){
                // errs()<<"0.LOAD GetVal error "<<rv->ID<<"\t"<<cfg->variableList[rv->ID].name<<"\n";
                assert(false && "Mk_ptr_operation_expr LOAD GetVal error!!");
            }  

			int allocaID = (int)val;
//          errs()<<"0.2 LOAD : "<<*con<<"\n";
            int addr = table->load(allocaID);
            if(addr>=0){
                Variable *rvr = table->getAlias(addr);
                table->setAlias(lv->ID, rvr->ID);
            }
            break;
        }
        case STORE:{
        	//	a = store b
        	//	PTR 	exprid
        	//	a 		b.exprid
    		double val = 0;
        	if(!table->getVal(lv->ID, val)){
                // errs()<<"Verifi store error "<<lv->ID<<"\t"<<lv->name<<"\n";
                assert(false && "Mk_ptr_operation_expr STORE GetVal error!!");
            }
            int allocaID = (int)val;

            Variable *rv = table->getAlias(rpv.rvar);

            if(rv->type!=PTR){
                z3::expr exprr = table->getX(rv->ID);
                if(time>=0)
                    table->setX(rv->ID, time, rv->type, rv->numbits, c);
                z3::expr exprl = table->getX(rv->ID);
                Expr = (exprl==exprr);
            }

            table->store(allocaID, rv->ID);
            break;
        }
        case ADDR:{
        	//	a = addr b
        	//	PTR 	allocaID
        	//	a 		b.exprid
            Variable *rv = table->getAlias(rpv.rvar);
            double rvrval = 0;
            table->setVal(lv->ID, rv->ID);
            if(!table->getVal(lv->ID,rvrval)){
                // errs()<<"Verifi ADDR error "<<*con<<"\t"<<rv->ID<<"\n";
                assert(false && "Mk_ptr_operation_expr ADDR GetVal error!!");
            }
            break;
        }
        case GETPTR:{
        	// 	c = a GETPTR a_0 a_1 a_2 .... e.g.
        	//	c = a GETPTR 0 1 2
        	//	PTR 	PTR 	PTR
        	//	a 	->	a_0 
        	// 		->	a_1 ->	a_1_0
        	// 				->	a_1_1
        	// 				->	a_1_2
 			/////////////////////////////////////////
        	//	PTR 	alias
        	//	c 		a_1_2
            Variable *rv = table->getAlias(rpv.varList[0]);
	     	double val = 0;
            int aliasID = rv->ID;
            for(unsigned i=1;i<rpv.varList.size()-1;i++){
                rv = table->getAlias(rpv.varList[i]);
                if(table->getVal(rv, val)){
                    aliasID+=val;
                    if(!table->getVal(aliasID, val)){
                        // errs()<<"0. Verifi GETPTR error "<<*con<<"\t"<<aliasID<<"\t"<<cfg->variableList[aliasID]<<"\n";
                        assert(false && "Mk_ptr_operation_expr aliasID GETPTR GetVal error!!");
                    }
                    aliasID = val;
                }
                else{
                    // errs()<<"1. Verifi GETPTR error "<<*con<<"\t"<<rv->ID<<"\n";
                    assert(false && "Mk_ptr_operation_expr rv GETPTR GetVal error!!");
                }
            }
            rv = table->getAlias(rpv.varList.back());
            if(table->getVal(rv, val)){
                aliasID+=val;
                table->setAlias(lv->ID, aliasID);
            }
            else{
                // errs()<<"2. Verifi GETPTR error "<<*con<<"\t"<<rv->ID<<"\n";
                assert(false && "Mk_ptr_operation_expr rv GETPTR GetVal error!!");
            }
            break;
        }
        case BITCAST:{
            // c = bitcast a
            //
        }
        default:   
        	assert(false && "Mk_ptr_operation_expr rpv.op error!!"); 
        	break;
    }

    return Expr;
}

z3::expr NonlinearZ3Verify::mk_convert_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time){

	z3::expr exprl(c); 
    z3::expr exprr(c);

	Op_m pvop = rpv.op;
    
    if(time>0)
    	table->setX(lv->ID, time, lv->type, lv->numbits, c);
    exprl = table->getX(lv->ID);

    Variable *rv = table->getAlias(rpv.rvar);

    bool treat = true;
    double rval = 0;
    z3::expr rv_expr = getExpr(rv, treat, rval, table);

    z3::expr temp(c);
    switch(pvop){
    	case TRUNC:{
    		//truncate a large size bit-vector to a small size bit-vector
    		assert(lv->type==INT && "Mk_convert_expr TRUNC error: lv is not integer type!!");
    		assert(rv->type==INT && "Mk_convert_expr TRUNC error: rv is not integer type!!");
    		assert(lv->numbits<rv->numbits && "Mk_convert_expr TRUNC error: lv numbits is larger than rv!!");

    		table->setX(lv->ID,rv_expr);
    		break;
    	}
    	case ZEXT:{
    		//Extend small size bit-vector with zeros to large size bit-vector 
    		assert(lv->type==INT && "Mk_convert_expr ZEXT error: lv is not integer type!!");
    		assert(rv->type==INT && "Mk_convert_expr ZEXT error: rv is not integer type!!");
    		assert(lv->numbits>rv->numbits && "Mk_convert_expr ZEXT error: lv numbits is smaller than rv!!");
            
            table->setX(lv->ID,rv_expr);
    		break;
    	}
    	case SEXT:{
    		//Extend small size bit-vector with sign bit to large size bit-vector 
    		assert(lv->type==INT && "Mk_convert_expr SEXT error: lv is not integer type!!");
    		assert(rv->type==INT && "Mk_convert_expr SEXT error: rv is not integer type!!");
    		assert(lv->numbits>rv->numbits && "Mk_convert_expr SEXT error: lv numbits is smaller than rv!!");

            table->setX(lv->ID,rv_expr);
    		break;
    	}
    	case FPTRUNC:{
    		//truncate a large size float point type to a small size float point type
    		//i.e. convert double to float now
    		assert((lv->type==FP && rv->type==FP) && "Mk_convert_expr FPTRUNC error: not floating-point type!!");
    		assert(lv->numbits<rv->numbits && "Mk_convert_expr FPTRUNC error: lv numbits is larger than rv!!");
    		
            table->setX(lv->ID,rv_expr);
    		break;
    	}
    	case FPEXT:{
    		//extend a small size float point  type to a large size float point type
    		//i.e. convert float to double now
    		assert((lv->type==FP && rv->type==FP) && "Mk_convert_expr FPEXT error:  not floating-point type!!");
    		assert(lv->numbits>rv->numbits && "Mk_convert_expr FPEXT error: lv numbits is smaller than rv!!");
    		
            table->setX(lv->ID,rv_expr);
    		break;
    	}
    	case FPTOUI:{
    		//Conversion of a floating-point term into an unsigned bit-vector.
    		assert(lv->type==INT && "Mk_convert_expr FPTOUI error: lv is not integer type!!");
    		assert(rv->type==FP && "Mk_convert_expr FPTOUI error: rv is not float type!!");

    		temp = ite((rv_expr>c.real_val(0)), ((exprl>(rv_expr-1))&&(exprl<=rv_expr)),((exprl<(rv_expr+1))&&(exprl>=rv_expr)));
    		rval = (int)rval;
    		break;
    	}
    	case FPTOSI:{
    		//Conversion of a floating-point term into a signed bit-vector.
    		assert(lv->type==INT && "Mk_convert_expr FPTOSI error: lv is not integer type!!");
    		assert(rv->type==FP && "Mk_convert_expr FPTOSI error: rv is not float type!!");
    		
            temp = ite((rv_expr>c.real_val(0)), ((exprl>(rv_expr-1))&&(exprl<=rv_expr)),((exprl<(rv_expr+1))&&(exprl>=rv_expr)));
    		rval = (int)rval;
    		break;
    	}
    	case UITOFP:{
    		//Conversion of a 2's complement unsigned bit-vector term into a term of Float Point sort.
    		assert(lv->type==FP && "Mk_convert_expr UITOFP error: lv is not float type!!");
    		assert(rv->type==INT && "Mk_convert_expr UITOFP error: rv is not integer type!!");

            table->setX(lv->ID,rv_expr);
    		break;
    	}
    	case SITOFP:{
    		//Conversion of a 2's complement signed bit-vector term into a term of Float Point sort.
    		assert(lv->type==FP && "Mk_convert_expr SITOFP error: lv is not float type!!");
    		assert(rv->type==INT && "Mk_convert_expr SITOFP error: rv is not integer type!!");

            table->setX(lv->ID,rv_expr);
    		break;
    	}
    	case BITCAST:{
    		assert(lv->numbits==rv->numbits && "Mk_convert_expr BITCAST error: Have different size type!!");

    		assert(false && "Mk_convert_expr BITCAST error: Bitcast with ptr can't handle yet!!");
    		break;
    	}
    	default:
    		assert(false && "Mk_convert_expr error: Op_m is not a conversion Operator!!");
    		break;
    }

    if(treat)
    	table->setVal(lv->ID, rval);

    return temp;
}

z3::expr NonlinearZ3Verify::mk_binaryop_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time){

	// z3::expr exprl(c); 
    z3::expr exprr(c);
    assert(rpv.isExp && "Mk_binaryop_expr error: rpv is not a expression!!");

	Op_m pvop = rpv.op;
    
    // if(time>0)
    // 	table->setX(lv->ID, time, lv->type, lv->numbits, c);
    // exprl = table->getX(lv->ID);

    Variable *rvl = table->getAlias(rpv.lvar);
    Variable *rvr = table->getAlias(rpv.rvar);

    bool treat = true;
    double rvlval = 0;
    double rvrval = 0;
    double rval = 0;
    z3::expr rvl_expr = getExpr(rvl, treat, rvlval, table);
    z3::expr rvr_expr = getExpr(rvr, treat, rvrval, table);

    z3::expr temp(c);

    switch(pvop){
    	case ADD:{
    		assert(lv->type==INT && "Mk_binaryop_expr ADD error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr ADD error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr ADD error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr ADD error: rvl and rvr have different interger type!!");

    		temp = (rvl_expr+rvr_expr);

    		if(treat)
    			rval = (int)rvlval+(int)rvrval;
    		break;
    	}
    	case SUB:{
    		assert(lv->type==INT && "Mk_binaryop_expr SUB error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr SUB error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr SUB error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr SUB error: rvl and rvr have different interger type!!");

    		temp = (rvl_expr-rvr_expr);

			if(treat)
    			rval = (int)rvlval-(int)rvrval;
    		break;
    	}
    	case MUL:{
    		assert(lv->type==INT && "Mk_binaryop_expr MUL error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr MUL error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr MUL error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr MUL error: rvl and rvr have different interger type!!");

    		temp = (rvl_expr*rvr_expr);

    		if(treat)
    			rval = (int)rvlval*(int)rvrval;
    		break;
    	}
    	case UDIV:{
    		assert(lv->type==INT && "Mk_binaryop_expr UDIV error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr UDIV error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr UDIV error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr UDIV error: rvl and rvr have different interger type!!");

    		temp = (rvl_expr/rvr_expr);

    		if(treat)
    			rval = (unsigned)rvlval/(unsigned)rvrval;
    		break;
    	}
    	case SDIV:{
    		assert(lv->type==INT && "Mk_binaryop_expr SDIV error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr SDIV error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr SDIV error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr SDIV error: rvl and rvr have different interger type!!");

    		temp = (rvl_expr/rvr_expr);

    		if(treat)
    			rval = (int)rvlval/(int)rvrval;
    		break;
    	}
    	case FADD:{
    		assert(lv->type==FP && "Mk_binaryop_expr FADD error: lv is not a float point type!!");
    		assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FADD error: rvl is not a float point type!!");
    		assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FADD error: rvr is not a float point type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FADD error: rvl and rvr have different float point type!!");

    		temp = (rvl_expr+rvr_expr);

    		if(treat)
    			rval = rvlval+rvrval;
    		break;
    	}
    	case FSUB:{
    		assert(lv->type==FP && "Mk_binaryop_expr FSUB error: lv is not a float point type!!");
    		assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FSUB error: rvl is not a float point type!!");
    		assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FSUB error: rvr is not a float point type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FSUB error: rvl and rvr have different float point type!!");

    		temp = (rvl_expr-rvr_expr);

    		if(treat)
    			rval = rvlval-rvrval;
    		break;
    	}
    	case FMUL:{
    		assert(lv->type==FP && "Mk_binaryop_expr FMUl error: lv is not a float point type!!");
    		assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FMUl error: rvl is not a float point type!!");
    		assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FMUl error: rvr is not a float point type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FMUl error: rvl and rvr have different float point type!!");

    		temp = (rvl_expr*rvr_expr);

    		if(treat)
    			rval = rvlval*rvrval;
    		break;
    	}
    	case FDIV:{
    		assert(lv->type==FP && "Mk_binaryop_expr FDIV error: lv is not a float point type!!");
    		assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FDIV error: rvl is not a float point type!!");
    		assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FDIV error: rvr is not a float point type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FDIV error: rvl and rvr have different float point type!!");

    		temp = (rvl_expr/rvr_expr);

    		if(treat)
    			rval = rvlval/rvrval;
    		break;
    	}
    	case UREM:{
    		assert(lv->type==INT && "Mk_binaryop_expr UREM error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr UREM error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr UREM error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr UREM error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm rem with nonlinear constraints!!");
    		temp = (rvl_expr+rvr_expr);

    		if(treat)
    			rval = (unsigned)rvlval%(unsigned)rvrval;
    		break;
    	}
    	case SREM:{
    		assert(lv->type==INT && "Mk_binaryop_expr SREM error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr SREM error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr SREM error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr SREM error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm rem with nonlinear constraints!!");

    		if(treat)
    			rval = (int)rvlval%(int)rvrval;
    		break;
    	}
    	case FREM:{
    		assert(lv->type==FP && "Mk_binaryop_expr FREM error: lv is not a float point type!!");
    		assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FREM error: rvl is not a float point type!!");
    		assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FREM error: rvr is not a float point type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FREM error: rvl and rvr have different float point type!!");

            assert(false && "Can't handle bit algorithm rem with nonlinear constraints!!");

    		treat = false;
    		break;
    	}
    	case LSHR:{
    		assert(lv->type==INT && "Mk_binaryop_expr LSHR error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr LSHR error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr LSHR error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr LSHR error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm lshr with nonlinear constraints!!");
    		treat = false;
    		break;
    	}
    	case ASHR:{
    		assert(lv->type==INT && "Mk_binaryop_expr ASHR error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr ASHR error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr ASHR error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr ASHR error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm ashr with nonlinear constraints!!");
    		treat = false;
    		break;
    	}
    	case SHL:{
    		assert(lv->type==INT && "Mk_binaryop_expr SHL error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr SHL error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr SHL error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr SHL error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm shl with nonlinear constraints!!");
    		treat = false;
    		break;
    	}
    	case AND:{
    		assert(lv->type==INT && "Mk_binaryop_expr AND error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr AND error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr AND error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr AND error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm and with nonlinear constraints!!");
    		treat = false;
    		break;
    	}
    	case NAND:{
    		assert(lv->type==INT && "Mk_binaryop_expr NAND error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr NAND error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr NAND error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr NAND error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm nand with nonlinear constraints!!");
    		treat = false;
    		break;
    	}
    	case OR:{
    		assert(lv->type==INT && "Mk_binaryop_expr OR error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr OR error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr OR error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr OR error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm or with nonlinear constraints!!");
    		treat = false;
    		break;
    	}
    	case XOR:{
    		assert(lv->type==INT && "Mk_binaryop_expr XOR error: lv is not a interger type!!");
    		assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr XOR error: rvl is not a interger type!!");
    		assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr XOR error: rvr is not a interger type!!");
    		assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr XOR error: rvl and rvr have different interger type!!");

            assert(false && "Can't handle bit algorithm xor with nonlinear constraints!!");
    		treat = false;
    		break;
    	}
    	default:
    		assert(false && "Mk_binaryop_expr error: Op_m is not a binary operator!!");
    		break;
    }

	if(treat)
        table->setVal(lv->ID, rval);

    table->setX(lv->ID, temp);
    return z3::expr(c);

    // return mk_eq_ast(exprl, exprr);;
}

z3::expr NonlinearZ3Verify::mk_compare_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time){
    assert(rpv.isExp && "Mk_compare_expr error: rpv is not a expression!!");

    assert((lv->type==INT&&lv->numbits==1) && "Mk_compare_expr error: lv is not a i1 type!!");

	Op_m pvop = rpv.op;
    
    if(time>0)
    	table->setX(lv->ID, time, lv->type, lv->numbits, c);
    z3::expr exprl = table->getX(lv->ID);

    Variable *rvl = table->getAlias(rpv.lvar);
    Variable *rvr = table->getAlias(rpv.rvar);

    bool treat = true;
    double rvlval = 0;
    double rvrval = 0;
    double rval = 0;
    z3::expr rvl_expr = getExpr(rvl, treat, rvlval, table);
    z3::expr rvr_expr = getExpr(rvr, treat, rvrval, table);

    z3::expr temp(c);

    switch(pvop){
    	case eq:case feq:  temp = (rvl_expr==rvr_expr);break;
    	case ne:case fne:  temp = (rvl_expr!=rvr_expr);break;
    	case slt:case ult:case flt:    temp = (rvl_expr<rvr_expr);break;
    	case sle:case ule:case fle:    temp = (rvl_expr<=rvr_expr);break;
    	case sgt:case ugt:case fgt:    temp = (rvl_expr>rvr_expr);break;
    	case sge:case uge:case fge:    temp = (rvl_expr>=rvr_expr);break;
    	default:	assert(false && "Mk_compare_expr error: Op_m is not a compare operator!!");break;
    }

    if(treat){
    	rval = getCMP(rvlval, rvrval, pvop);
    	table->setVal(lv->ID, rval);
    }
    z3::expr ast = ite(temp, c.int_val(1), c.int_val(0));

    table->setX(lv->ID, ast);
    return z3::expr(c);

    // return ast;
}

z3::expr NonlinearZ3Verify::mk_function_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time){
	// z3::expr exprl(c); 
    // z3::expr exprr(c);
    assert(rpv.isExp && "Mk_compare_expr error: rpv is not a expression!!");

	Op_m pvop = rpv.op;
    
    // if(time>0)
    // 	table->setX(lv->ID, time, lv->type, lv->numbits, c);
    // exprl = table->getX(lv->ID);

    Variable *rv = table->getAlias(rpv.rvar);

    bool treat = true;
    double rval = 0;
    z3::expr rv_expr = getExpr(rv, treat, rval, table);

    z3::expr temp(c);

    switch(pvop){
    	case ABS:{
    		assert(rv->type==INT||rv->type==INTNUM && "Mk_function_expr ABS error: rv is not an integer type!!");
    		z3::expr cond = (rv_expr>=c.int_val(0));
    		temp = ite(cond, rv_expr, -rv_expr);
    		break;
    	}
    	case FABS:{
    		assert(rv->type==FP||rv->type==FPNUM && "Mk_function_expr FABS error: rv is not a float point type!!");
            z3::expr cond = (rv_expr>=c.real_val(0));
            temp = ite(cond, rv_expr, -rv_expr);
    		break;
    	}
    	case POW:{
            rv = table->getAlias(rpv.lvar);
            z3::expr rvl_expr = getExpr(rv, treat, rval, table);
            temp = pw(rvl_expr, rv_expr);
            break;
        }
        case SQRT:{
            temp = pw(rv_expr, c.real_val("0.5"));
            break;
        }
        case COPYSIGN:{
            rv = table->getAlias(rpv.lvar);
            z3::expr rvl_expr = getExpr(rv, treat, rval, table);
            z3::expr sign_cmp_expr = ((rvl_expr * rv_expr) > 0);
            temp = ite(sign_cmp_expr, rvl_expr, -rvl_expr);
        }
        case FMAX:{
            rv = table->getAlias(rpv.lvar);
            z3::expr rvl_expr = getExpr(rv, treat, rval, table);
            temp = ite((rvl_expr>rv_expr), rvl_expr, rv_expr);
        }
        case FMIN:{
            rv = table->getAlias(rpv.lvar);
            z3::expr rvl_expr = getExpr(rv, treat, rval, table);
            temp = ite((rvl_expr<rv_expr), rvl_expr, rv_expr);
        }
        case FDIM:{
            rv = table->getAlias(rpv.lvar);
            z3::expr rvl_expr = getExpr(rv, treat, rval, table);
            temp = ite((rvl_expr>rv_expr), (rvl_expr - rv_expr), c.int_val(0));
        }
    	default:
    		assert(false && "Mk_function_expr error: Op_m is not a function operator!!");
    		break;
    }
    
    table->setX(lv->ID, temp);
    return z3::expr(c);

    // return mk_eq_ast(exprl, exprr);
}


/* transform constraints into smt2 with z3 api */
bool NonlinearZ3Verify::get_constraint(Constraint *con, NonlinearZ3VarTable *table, int time, z3::expr_vector &p){

    // if(outMode)
    //     errs()<<*con<<"\n";
    dbg->getConsInfo(con);
    Operator op = con->op;
    
    z3::expr exprl(c); 
    z3::expr exprr(c);
    z3::expr ast(c); 

    ParaVariable lpv,rpv;

    switch(op){
        case EQ:case NE:
        case SLT:case SLE:case SGT:case SGE:
        case ULT:case ULE:case UGT:case UGE:
        case FEQ:case FNE:
        case FLT:case FLE:case FGT:case FGE:{
            ast = mk_compare_ast(con, table);
            break;
        }
        case ASSIGN:{
        	ast = mk_assignment_ast(con, table, time);
        	break;
        	/*
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp)
                errs()<<"get_constraint error: isExp6\n";
            lv = table->getAlias(lpv.rvar);
            
            if(lv->type==PTR){
                if(!rpv.isExp){
                    rv = table->getAlias(rpv.rvar);
                    if(rv->type==PTR){
                        table->setAlias(lv, rv);
                    }
                    else
                        errs()<<"get_constraint error: PTR rv->type error1\n";
                }
                else{
                    Op_m pvop = rpv.op;
                    Variable *rvr=NULL;
                    double rvrval = 0;
                    double val = 0;
                    int allocaID,addr,aliasID;
                    switch(pvop){
                        case GETPTR:
                            rv = table->getAlias(rpv.varList[0]);
                            aliasID = rv->ID;
                            for(unsigned i=1;i<rpv.varList.size()-1;i++){
                                rv = table->getAlias(rpv.varList[i]);
                                if(table->getVal(rv, val)){
                                    aliasID+=val;
                                    if(!table->getVal(aliasID, val)&&outMode==1)
                                        errs()<<"0. Verifi GETPTR error "<<*con<<"\t"<<aliasID<<"\t"<<cfg->variableList[aliasID]<<"\n";
                                    aliasID = val;
                                }
                                else
                                    errs()<<"1. Verifi GETPTR error "<<*con<<"\t"<<rv->ID<<"\n";
                            }
                            rv = table->getAlias(rpv.varList.back());
                            if(table->getVal(rv, val)){
                                aliasID+=val;
                                table->setAlias(lv->ID, aliasID);
                            }
                            else if(outMode==1)
                                errs()<<"2. Verifi GETPTR error "<<*con<<"\t"<<rv->ID<<"\n";
                            break;
                        case ADDR:
                            rv = table->getAlias(rpv.rvar);
                            table->setVal(lv->ID, rv->ID);
                            if(!table->getVal(lv->ID,rvrval)&&outMode==1)
                                errs()<<"Verifi ADDR error "<<*con<<"\t"<<rv->ID<<"\n";
                            break;
                        case STORE:
                            if(!table->getVal(lv->ID, val)&&outMode==1)
                                errs()<<"Verifi store error "<<lv->ID<<"\t"<<lv->name<<"\n";
                            allocaID = (int)val;
                            rv = table->getAlias(rpv.rvar);
                            table->store(allocaID, rv->ID);
                            break;
                        case LOAD:
                            rv = table->getAlias(rpv.rvar);
                            if(!table->getVal(rv->ID, val)&&outMode==1)
                                errs()<<"0.LOAD GetVal error "<<rv->ID<<"\t"<<cfg->variableList[rv->ID].name<<"\n";    
//
                            allocaID = (int)val;
//                            errs()<<"0.2 LOAD : "<<*con<<"\n";
                            addr = table->load(allocaID);
                            if(addr>=0){
                                rvr = table->getAlias(addr);
                                table->setAlias(lv->ID, rvr->ID);
                            }
                            break;
                        case ALLOCA:
                            allocaID = table->alloca();
                            table->setVal(lv->ID, allocaID);
                            break;
                        default:    
                            errs()<<"get_constraint error: PTR rpv.op error "<<*con<<"\n";
                    }
                }
                return;
            }
            else if(lv->type==INT||lv->type==FP){
                if(time>1)
                    table->setX(lv->ID, time, lv->type, c);
                exprl = table->getX(lv->ID);

                if(!rpv.isExp){
                    rv = table->getAlias(rpv.rvar);
                    if(rv->type==FPNUM){
                        exprr = c.real_val(getRealVal(rv->name));
                        double val = ConvertToDouble(rv->name);
                        table->setVal(lv->ID, val);
                    }
                    else if(rv->type==INTNUM){
                        exprr = c.int_val(getRealVal(rv->name));
                        double val = ConvertToDouble(rv->name);
                        table->setVal(lv->ID, val);
                    }
                    else if(rv->type==INT || rv->type==FP){
                        exprr = table->getX(rv->ID);
                        double val;
                        if(lv->type==INT && rv->type==FP){
                            z3::expr ast_tleq(c);
                            z3::expr ast_tgt(c);
                            z3::expr ast_and(c);
                            ast_tleq = exprl<=exprr; 
                            ast_tgt = exprl>(exprr-c.real_val(1));
                            ast_and = ast_tleq&&ast_tgt;
                            
                            if(table->getVal(rv->ID, val))
                                table->setVal(lv->ID, (int)val);
                            if(outMode)
                                cerr<<ast_and<<"\n";
                            p.push_back(ast_and);
                            return;
                        }
                        else{
                            if(table->getVal(rv->ID, val))
                                table->setVal(lv->ID, val);
                        }
                    }
                    else
                        errs()<<"get_constraint error: DATA rv->type error\n";
                }
                else{
                    Op_m pvop = rpv.op;
                    Variable *rvl=NULL;
                    Variable *rvr=NULL;
                    double rl=0;
                    double rr=0;
                    double val=0;
                    z3::expr y(c);
                    z3::expr z(c);
                    string name = lv->name;
                    bool treat = true;
                    switch(pvop){
                        case LOAD:
                            rvr = table->getAlias(rpv.rvar);
                            if(!table->getVal(rvr->ID, val)&&outMode==1)
                                errs()<<"2.LOAD GetVal error "<<rvr->ID<<"\t"<<cfg->variableList[rvr->ID].name<<"\n";    
                            rl = (int)val;
                            rr = table->load(rl);
                            treat = table->getVal(rr, val);
                            if(treat)
                                table->setVal(lv->ID, val);
                            exprr = table->getX(rr);
                            break;
                        case AND:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);     
                            exprr = bvcal (y, z, pvop);    
                            // cerr<<exprr<<endl;
                            if(treat)
                                table->setVal(lv->ID, (int)rl&(int)rr);
                            break;
                        case NAND:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);   
                            exprr = bvcal(y, z, pvop);    
                            if(treat)
                                table->setVal(lv->ID, ~((int)rl&(int)rr));
                            break;
                        case OR:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);   
                            exprr = bvcal(y, z, pvop);    
                            if(treat)
                                table->setVal(lv->ID, (int)rl|(int)rr);
                            break;
                        case XOR:
                        	cerr<<"124124345346431231"<<endl;
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);  
                            cerr<<"XOR:"<<z<<"\n"; 
                            exprr = bvcal(y, z, pvop);
                            cerr<<"XOR:"<<exprr<<"\n";
                            if(treat)
                                table->setVal(lv->ID, (int)rl^(int)rr);
                            break;
                        case SREM:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);   
                            exprr = bvcal(y, z, pvop);    
                            if(treat)
                                table->setVal(lv->ID, (int)rl%(int)rr);
                            break;
                        case ASHR:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            if(!treat)
                                errs()<<"ASHR error: invalid z value\n";
                            y = getExpr(rvl, treat, rl, table);   
                            exprr = bvcal(y, z, pvop);    
                            if(treat)
                                table->setVal(lv->ID, (int)rl>>(int)rr);
                            break;
                        case SHL:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            if(!treat)
                                errs()<<"SHL error: invalid z value\n";
                            y = getExpr(rvl, treat, rl, table);   
                            exprr = bvcal(y, z, pvop);    
                            if(treat)
                                table->setVal(lv->ID, (int)rl<<(int)rr);
                            break;
                        case ADD:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = y+z;
                            if(treat)
                                table->setVal(lv->ID, rl+rr);
                            break;
                        case SUB:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = y-z;
                            if(treat)
                                table->setVal(lv->ID, rl-rr);
                            break;
                        case POW:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = pw(y, z);
                            if(treat)
                                table->setVal(lv->ID, powf(rl,rr));
                            break;
                        case MUL:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = y*z;
                            if(treat)
                                table->setVal(lv->ID, rl*rr);
                            break;
                        case DIV:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = y/z;
                            if(treat&&rr!=0)
                                table->setVal(lv->ID, rl/rr);
                            break;
                        case lt:case le:case gt:case ge:case eq:case ne:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = mk_INT_cmp(y, z, pvop);
                            if(treat)
                                table->setVal(lv->ID, getCMP(rl, rr ,pvop));
                            break;
                        default:
                            errs()<<"get_constraint error: DATA rpv.op error "<<*con<<"\n";
                    }
                }
            }
            else
                errs()<<"get_constraint error: lv->type error\n";
            ast = (exprl==exprr);
            break;
            */
        }
        default:
        	assert(false && "Get_constraint error: Nonlinear operator!!");
        	break;
    }

    if(ast){
	    if(outMode==1){
	        cerr<<ast<<"\n";
	    }
	    p.push_back(ast);
	    return true;
	}
	
	// if(outMode==1){
	//     cerr<<"......"<<"\n";
	// }
    return false;
}


/*encode the abstract into a linear costraint set */
z3::expr_vector NonlinearZ3Verify::encode_path(CFG* ha, vector<int> &patharray){
    NonlinearZ3VarTable *table = new NonlinearZ3VarTable(c, ha);

    int state_num=(patharray.size()+1)/2;
    int total_state  = ha->stateList.size()+ ha->transitionList.size();
    vector<int> repeat(total_state,0);
    z3::expr_vector problem(c);
    
    for (int j= 0;j<state_num; j++){ 
        int ID = patharray[2*j];
        State* st=ha->searchState(ID);
        assert(st!=NULL);
        if(outMode==1)
            errs()<<st->name<<":\n";
        //encode the previous transition guard
        for(unsigned m=0;m<st->consList.size();m++){
            Constraint* con = &st->consList[m];
            bool getCon = get_constraint(con, table, repeat[ID], problem);
            if(getCon)	index_cache.push_back(IndexPair(j,j));
        }
        repeat[ID]+=1;
        if(j!=state_num-1)    {
            ID = patharray[2*j+1];
            Transition* pre=ha->searchTransition(ID);
            assert(pre!=NULL);
            if(outMode==1)
                errs()<<pre->name<<":\n";
            //encode the previous transition guard    
            
            for(unsigned m=0;m<pre->guardList.size();m++){
                Constraint* con = &pre->guardList[m];
                bool getCon = get_constraint(con, table, repeat[ID], problem);
                if(getCon)	index_cache.push_back(IndexPair(j,j+1));
            }
            repeat[ID]+=1;
        }
    }

    errs()<<"Encode end\n";
    delete table;
    return problem;
}

/* analyze the unsat core to extract the infeasible path segment */
bool NonlinearZ3Verify::analyze_unsat_core(SubsetSolver& csolver, MapSolver& msolver){

    cerr<<"Solving constraints~~~\n";
    for(int k=0;k<MUS_LIMIT;k++){
        vector<int> seed = msolver.next_seed();
        errs()<<"\n"<<"seed"<<"\n";
        printVector(seed);
        if(seed.size() == 0)
            break;
        if(!csolver.check_subset(seed)){
            vector<int> MUS = seed;
            errs()<<"\n"<<"MUS"<<"\n";
            printVector(MUS);
            int from = INT_MAX, to = 0;
            if(Nonlinear_VERBOSE_LEVEL>2) printf("MUS:\n");
            for(unsigned i=0;i<MUS.size();i++){
                if(Nonlinear_VERBOSE_LEVEL>2)
                     cout<<csolver.get_constraint(MUS[i])<<"\n";
                int start = index_cache[MUS[i]].start;
                int end   = index_cache[MUS[i]].end;                                                                
                if(from>start)
                    from = start;
                if(to<end)
                    to = end;
            }
            add_IIS(IndexPair(from,to));
            if(Nonlinear_UC_LEVEL == 0) break;
            msolver.block_up(MUS);
        }
        else{
            if(seed.size() == csolver.size())
                return false;
            msolver.block_down(seed);
        }
    }
    return true;
}


/* add unsat core into cache */
void NonlinearZ3Verify::add_IIS(IndexPair index){
	errs()<<"IIS:\t";
	index.print();
	errs()<<"\n";
    for(unsigned i=0;i<core_index.size();i++){
        if(index.contain(core_index[i])){
          core_index[i] = index;
          return;
        }
        else if(core_index[i].contain(index))
          return;
    }
    core_index.push_back(index);
}

/*      analyse nonlinear constraints       */
bool NonlinearZ3Verify::analyze_nonlinear(z3::expr_vector problem){

    z3::solver s(c);
    unsigned size = problem.size();
    for(unsigned i=0;i<size;++i){
        s.add(problem[i]);
    }
    if(outMode==1){
        // cerr<<s.to_smt2()<<endl;
        cerr<<s.check()<<endl;
    }
    return (s.check()==z3::check_result::unsat);
}
