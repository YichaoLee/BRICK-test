#include "LinearVerify.h"
#include "time.h"
#include "float.h"
using namespace std;
int VERBOSE_LEVEL = 0;
int UC_LEVEL=0;

//add constraint to empty vector  0==0


 void printVector(vector<int> path){
    for(vector<int>::iterator it=path.begin();it<path.end();it++)
        errs()<<*it<<";";
    errs()<<"\n";
}

/***************************table of variables in linear constraints*********************************/
    LinearVarTable::LinearVarTable(z3::context &ctx, CFG *ha){
        cfg = ha;
        unsigned inputID=0;
        var_num = 0;
        alloca_num = 0;
//        for(int i=0; i<cfg->mainInput.size();i++)
//            errs()<<"LinearVarTable initial "<<cfg->mainInput[i]<<"\t"<<cfg->variableList[cfg->mainInput[i]].name<<"\n";
        for(unsigned i=0;i<cfg->variableList.size();i++)
        {
            Variable var =  cfg->variableList[i];
            VarType type = var.type;

            if(inputID<cfg->mainInput.size()&&cfg->mainInput[inputID]==(int)i){

                if(type==FP)
                    x.push_back(ctx.real_const(var.name.c_str()));
                else if(type==INT)
                    x.push_back(ctx.int_const(var.name.c_str()));
                exprMap[i] = var_num;
                inputID++;
                var_num++;
            }
            else if(type==FP){
                x.push_back(ctx.real_const(var.name.c_str()));
                exprMap[i] = var_num; 
                var_num++;
            }
            else if(type==INT){
                x.push_back(ctx.int_const(var.name.c_str()));
                exprMap[i] = var_num; 
                var_num++;
            }
        }
    }

    LinearVarTable::~LinearVarTable(){varVal.clear();alias.clear();storeMap.clear();exprMap.clear();x.clear();var_num=0;alloca_num=0;cfg=NULL;}

    void LinearVarTable::setX(int ID, int time, VarType type, z3::context &ctx){
        int ID2 = exprMap[ID];
        if(type==FP)
            x[ID2] = ctx.real_const((cfg->variableList[ID].name+"_"+int2string(time)).c_str());
        else if(type==INT)
            x[ID2] = ctx.int_const((cfg->variableList[ID].name+"_"+int2string(time)).c_str());
        else
            errs()<<"SetX error 10086!!\n";
    }

    int LinearVarTable::alloca(){
        storeMap[++alloca_num] = -2;
        return alloca_num;
    }

    void LinearVarTable::setAlias(int ID1, int ID2){
        alias[ID1] = ID2;
    }

    void LinearVarTable::setAlias(Variable *v1, Variable *v2){
        int ID1=v1->ID;
        int ID2=v2->ID;
        alias[ID1] = ID2;
    }

    void LinearVarTable::setVal(int ID, double val){
        varVal[ID] = val;
    }

    void LinearVarTable::store(int ID1, int ID2){
        storeMap[ID1] = ID2;
    }

    int LinearVarTable::getNum(){
        return var_num;    
    }
    
    z3::expr LinearVarTable::getX(int ID){
        int ID2 = exprMap[ID];
        return x[ID2];
    }

    int LinearVarTable::load(int ID){
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
    bool LinearVarTable::hasAlias(Variable *v){
        int ID = v->ID;
        int count = alias.count(ID);
        if(count)
            return true;
        else
            return false;
    }

    Variable* LinearVarTable::getAlias(int ID){
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

    Variable* LinearVarTable::getAlias(Variable* var){
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

    bool LinearVarTable::getVal(Variable *var, double &v){
        if(var->type==INTNUM||var->type==FPNUM){
            v=ConvertToDouble(var->name);
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

    bool LinearVarTable::getVal(int ID, double &v){
        int count = varVal.count(ID);
        if(count){
            v = varVal[ID];
            return true;
        }
        else{
            return false;
        }
    }

    map<int, double> LinearVarTable::getValmap(){
           return varVal;
    }

    map<int, int> LinearVarTable::getAliasmap(){
           return alias;
    }

    CFG *LinearVarTable::getCFG(){
        return cfg;
    }

/********************************class LinearVerify***********************************/
/*******************************solution of linear problems by z3**********************************/
/* verify the feasibility of the path return true:sat false:unsat  */

bool LinearVerify::check(CFG* ha, vector<int> path){
    clear();

    if(outMode==1)
        printPath(ha, path);

    try{
        //ha->print();
        //printVector(path);
        clock_t start,finish;

        z3::expr_vector problem = encode_path(ha, path);
        start = clock();

        SubsetSolver csolver(c, problem);
        MapSolver msolver(csolver.size());
        bool res = analyze_unsat_core(csolver, msolver);

        finish=clock();

        time = 1000*(double)(finish-start)/CLOCKS_PER_SEC;
        
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

void LinearVerify::print_sol(CFG *cfg){

}

z3::expr LinearVerify::getExpr(Variable *v, bool &treat, double &val, LinearVarTable *table)
{
    z3::expr Expr(c);
    if(v->type==FPNUM){
        Expr = c.real_val(getRealVal(v->name));
        val = ConvertToDouble(v->name);
    }
    else if(v->type==INTNUM){
        Expr = c.int_val(getRealVal(v->name));
        val = ConvertToDouble(v->name);
    }
    else if(v->type == INT || v->type==FP){
        Expr = table->getX(v->ID);
        treat = treat&table->getVal(v->ID, val);
    }
    else
        errs()<<"getExpr error : v->type error\n";
    return Expr;
}

z3::expr LinearVerify::mk_INT_cmp(z3::expr y, z3::expr z, Op_m pvop){
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

int LinearVerify::getCMP(int rl, int rr, Op_m pvop){
    bool cmp=false;
    switch(pvop){
        case lt:cmp = (rl<rr);break;
        case le:cmp = (rl<=rr);break;
        case gt:cmp = (rl>rr);break;
        case ge:cmp = (rl>=rr);break;
        case eq:cmp = (rl==rr);break;
        case ne:cmp = (rl!=rr);break;
        default:assert(false);
    }
    if(cmp)
        return 1;
    return 0;
}

char const* LinearVerify::getRealVal(string str){
    int plusID = str.find("e+");
    if(plusID!=-1){
        plusID++;
        return str.erase(plusID, 1).c_str();
    }
    return str.c_str();
}

z3::expr LinearVerify::getCMPExpr(Variable *v, LinearVarTable *table){
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

z3::expr LinearVerify::bvcal(z3::expr a, z3::expr b, Op_m op){
	

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

/* transform constraints into smt2 with z3 api */
void LinearVerify::get_constraint(Constraint *con, LinearVarTable *table, int time, z3::expr_vector &p){
	errs()<<*con<<"\n";
    dbg->getConsInfo(con);
    Operator op = con->op;
    
    z3::expr exprl(c); 
    z3::expr exprr(c);
    z3::expr ast(c); 
    
    CFG *cfg = table->getCFG();

    ParaVariable lpv,rpv;
    Variable *lv;
    Variable *rv;
    int ID1,ID2;

    switch(op){
        case LT:
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp1\n";
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.LT GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.LT GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = c.real_val(ConvertToString(lval).c_str());
                exprr = c.real_val(ConvertToString(rval).c_str());
            }
            else{
                exprl = getCMPExpr(lv, table);
				exprr = getCMPExpr(rv, table);
            }
            ast = exprl<exprr;
            break;
        case LE:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp2\n";
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.LE GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.LE GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = c.real_val(ConvertToString(lval).c_str());
                exprr = c.real_val(ConvertToString(rval).c_str());
            }
            else{
                exprl = getCMPExpr(lv, table);
				exprr = getCMPExpr(rv, table);
            }
            ast = exprl<=exprr;
            break;
        case GT:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp3\n";
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.GT GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.GT GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = c.real_val(ConvertToString(lval).c_str());
                exprr = c.real_val(ConvertToString(rval).c_str());
            }
            else{
                exprl = getCMPExpr(lv, table);
				exprr = getCMPExpr(rv, table);
            }
            ast = exprl>exprr;
            break;
        case GE:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp4\n";    
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.GE GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.GE GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = c.real_val(ConvertToString(lval).c_str());
                exprr = c.real_val(ConvertToString(rval).c_str());
            }
            else{
               	exprl = getCMPExpr(lv, table);
				exprr = getCMPExpr(rv, table);
            }
            ast = exprl>=exprr;
            break;
        case EQ:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp5\n";    
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.EQ GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.EQ GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = c.real_val(ConvertToString(lval).c_str());
                exprr = c.real_val(ConvertToString(rval).c_str());
            }
            else{
                exprl = getCMPExpr(lv, table);
				exprr = getCMPExpr(rv, table);
            }
            if(!z3::eq(exprl.get_sort(), exprr.get_sort())){
		        exprl = to_real(exprl);
		        exprr = to_real(exprr);
		    }
            ast = exprl==exprr;
            break;
        case NE:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp5\n";    
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.NE GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.NE GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = c.real_val(ConvertToString(lval).c_str());
                exprr = c.real_val(ConvertToString(rval).c_str());
            }
            else{
                exprl = getCMPExpr(lv, table);
				exprr = getCMPExpr(rv, table);
            }
            if(!z3::eq(exprl.get_sort(), exprr.get_sort())){
		        exprl = to_real(exprl);
		        exprr = to_real(exprr);
		    }
            ast = exprl!=exprr;
            break;
        case ASSIGN:{
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
        }
    }
    if(outMode==1){
        cerr<<ast<<"\n";
    }
    p.push_back(ast);
    return;
}


/*encode the abstract into a linear costraint set */
z3::expr_vector LinearVerify::encode_path(CFG* ha, vector<int> patharray){
    LinearVarTable *table = new LinearVarTable(c, ha);

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
            get_constraint(con, table, repeat[ID], problem);
            repeat[ID]+=1;
            index_cache.push_back(IndexPair(j,j));
        }
        if(j!=state_num-1)    {
            ID = patharray[2*j+1];
            Transition* pre=ha->searchTransition(ID);
            assert(pre!=NULL);
            if(outMode==1)
                errs()<<pre->name<<":\n";
            //encode the previous transition guard    
            
            for(unsigned m=0;m<pre->guardList.size();m++){
                Constraint* con = &pre->guardList[m];
                get_constraint(con, table, repeat[ID], problem);
                repeat[ID]+=1;
                index_cache.push_back(IndexPair(j,j+1));
            }
        }
    }

    return problem;
}

/* analyze the unsat core to extract the infeasible path segment */
bool LinearVerify::analyze_unsat_core(SubsetSolver& csolver, MapSolver& msolver){
    for(int k=0;k<MUS_LIMIT;k++){
        vector<int> seed = msolver.next_seed();
        //errs()<<"\n"<<"seed"<<"\n";
        //printVector(seed);
        //errs()<<"\n"<<"MUS"<<"\n";
        if(seed.size() == 0)
            break;
        if(!csolver.check_subset(seed)){
            vector<int> MUS = csolver.shrink(seed);
        //printVector(MUS);
        //errs()<<"\n";
            int from = INT_MAX, to = 0;
            if(VERBOSE_LEVEL>2) printf("MUS:\n");
            for(unsigned i=0;i<MUS.size();i++){
                if(VERBOSE_LEVEL>2)
                     cout<<csolver.get_constraint(MUS[i])<<"\n";
                int start = index_cache[MUS[i]].start;
                int end   = index_cache[MUS[i]].end;                                                                
                if(from>start)
                    from = start;
                if(to<end)
                    to = end;
            }
            add_IIS(IndexPair(from,to));
            if(UC_LEVEL == 0) break;
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
void LinearVerify::add_IIS(IndexPair index){
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

