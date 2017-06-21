
#include "NonlinearVerify.h"
#include "time.h"
#include "float.h"
using namespace std;

/***********************  Class NonlinearVarTable  *********************/

    NonlinearVarTable::NonlinearVarTable(dreal_context &c, CFG *ha):ctx(c), cfg(ha){
        unsigned inputID=0;
        var_num = 0;
        alloca_num = 0;
        // for(int i=0; i<cfg->mainInput.size();i++)
        //     errs()<<"NonlinearVarTable initial "<<cfg->mainInput[i]<<"\t"<<cfg->variableList[cfg->mainInput[i]].name<<"\n";
        for(unsigned i=0;i<cfg->variableList.size();i++)
        {

            Variable var =  cfg->variableList[i];
            VarType type = var.type;

            if(inputID<cfg->mainInput.size()&&cfg->mainInput[inputID]==i){

                if(type==FP)
                    // x.push_back(dreal_mk_real_var(ctx, var.name.c_str(), -1000.0, 1000.0));
                    x.push_back(dreal_mk_unbounded_real_var(ctx, var.name.c_str()));
                else if(type==INT)
                    // x.push_back(dreal_mk_int_var(ctx, var.name.c_str(), -1000.0, 1000.0));
                    x.push_back(dreal_mk_unbounded_int_var(ctx, var.name.c_str()));
                exprMap[i] = var_num;
//                double const x_lb = dreal_get_lb(ctx, x[var_num]);
//                double const x_ub = dreal_get_ub(ctx, x[var_num]);
//                errs()<<var.name<<" = ["<<x_lb<<", "<<x_ub<<"]\n";
                inputID++;
                var_num++;
            }
            else if(type==FP){
                x.push_back(dreal_mk_unbounded_real_var(ctx, var.name.c_str()));
                exprMap[i] = var_num; 
                var_num++;
            }
            else if(type==INT){
                x.push_back(dreal_mk_unbounded_int_var(ctx, var.name.c_str()));
                exprMap[i] = var_num; 
                var_num++;
            }

        }
    }

    NonlinearVarTable::~NonlinearVarTable(){
        varVal.clear();
        alias.clear();
        storeMap.clear();
        exprMap.clear();
        x.clear();
        cfg=NULL;
    }


    void NonlinearVarTable::setX(int ID, int time, VarType type){
        int ID2 = exprMap[ID];
        if(type==FP)
            x[ID2] = dreal_mk_unbounded_real_var(ctx, (cfg->variableList[ID].name+"/t"+int2string(time)).c_str());
        else if(type==INT)
            x[ID2] = dreal_mk_unbounded_int_var(ctx, (cfg->variableList[ID].name+"/t"+int2string(time)).c_str());
        else
            assert(false && "SetX error 10086!!");
    }
    int NonlinearVarTable::alloca(){
        storeMap[++alloca_num] = -2;
        return alloca_num;
    }
    void NonlinearVarTable::setAlias(int ID1, int ID2){
        int count = alias.count(ID2);
        if(count)
            ID2 = alias[ID2];
        alias[ID1] = ID2;
        // errs()<<"setAlias: ";
        // errs()<<cfg->variableList[ID1]<<"\t\t"<<cfg->variableList[ID2]<<"\n";
    }
    void NonlinearVarTable::setAlias(Variable *v1, Variable *v2){
        int ID1=v1->ID;
        int ID2=v2->ID;
        int count = alias.count(ID2);
        if(count)
            ID2 = alias[ID2];
        alias[ID1] = ID2;
        // errs()<<"setAlias: ";
        // errs()<<cfg->variableList[ID1]<<"\t\t"<<cfg->variableList[ID2]<<"\n";
    }
    void NonlinearVarTable::setVal(int ID, double val){
        varVal[ID] = val;
    }
    void NonlinearVarTable::store(int ID1, int ID2){
        storeMap[ID1] = ID2;
    }

    int NonlinearVarTable::getNum(){
        return var_num;    
    }
    
    dreal_expr NonlinearVarTable::getX(int ID){
        int count = alias.count(ID);
        if(count)
            ID = alias[ID];
        int ID2 = exprMap[ID];
        return x[ID2];
    }

    void NonlinearVarTable::setX(int ID, dreal_expr expr){
    	int count = alias.count(ID);
        if(count)
            ID = alias[ID];
        int ID2 = exprMap[ID];
        x[ID2] = expr;
    }

    int NonlinearVarTable::load(int ID){
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
    bool NonlinearVarTable::hasAlias(Variable *v){
        int ID = v->ID;
        int count = alias.count(ID);
        if(count)
            return true;
        else
            return false;
    }

    Variable* NonlinearVarTable::getAlias(int ID){
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

    Variable* NonlinearVarTable::getAlias(Variable* var){
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
    bool NonlinearVarTable::getVal(Variable *var, double &v){
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
    bool NonlinearVarTable::getVal(int ID, double &v){
        int count = varVal.count(ID);
        if(count){
            v = varVal[ID];
            return true;
        }
        else{
            return false;
        }
    }
    void NonlinearVarTable::printAliasMap(){
    	errs()<<"AliasMap:\n";
        for(map<int,int>::iterator it=alias.begin();it!=alias.end();++it){
            errs()<<cfg->variableList[it->first]<<"\t\t"<<cfg->variableList[it->second]<<"\n";
        }
    }
    map<int, double> NonlinearVarTable::getValmap(){
           return varVal;
    }
    map<int, int> NonlinearVarTable::getAliasmap(){
           return alias;
    }
    CFG *NonlinearVarTable::getCFG(){
        return cfg;
    }


/****************** Class NonlinearVerify ******************/

/***********************************check with dReal*********************************************/
NonlinearVerify::NonlinearVerify(){
    dreal_init();
    ctx = s.get_ctx();
    table=NULL;
    solverTime=0;
}

NonlinearVerify::NonlinearVerify(double pre, DebugInfo *d, int mode){
    dreal_init();
    ctx = s.get_ctx();
    table=NULL;
    this->precision = pre;
    dreal_set_precision(ctx, pre);
    this->dbg = d;
    this->outMode = mode;
    solverTime=0;
} 

NonlinearVerify::~NonlinearVerify(){
    clear();
}

bool NonlinearVerify::check(CFG* ha, vector<int> &path)
{
    reset();
    
    if(outMode==1)
        printPath(ha, path);
    
    int state_num=(path.size()+1)/2;
    clock_t start,finish;

//    double pre = dreal_get_precision(ctx);
//    cerr<<"Precision is "<<pre<<endl;

    encode_path(ha, path);

    start = clock();
//    dreal_use_polytope(ctx);

    bool res = analyze_unsat_core(state_num-1);

    finish=clock();

    solverTime = 1000*(double)(finish-start)/CLOCKS_PER_SEC;
//        errs()<<"Time:\t"<<ConvertToString(time_used)<<"ms\n";

    // print_sol(ha);
    if(res == true){
        if(outMode==1)
            cerr<<"dreal_result is sat\n\n\n";
        return true;
    }
    if(outMode==1)
        cerr<<"dreal_result is unsat\n\n\n";
    return false;
}

void NonlinearVerify::print_sol(CFG* cfg) {
    vector<unsigned> &x = cfg->mainInput;
    for(unsigned i=0;i<x.size();i++){
        errs()<<cfg->variableList[x[i]].name<<" = [";
        dreal_expr mainInput = table->getX(static_cast<int>(x[i]));

        double const x_lb = dreal_get_lb(ctx, mainInput);
        double const x_ub = dreal_get_ub(ctx, mainInput);
        errs()<<x_lb<<", "<<x_ub<<"]\n";
    }
    return;
}

// dreal_expr NonlinearVerify::getExpr(Variable *v, bool &treat, double &val, NonlinearVarTable *table)
// {
//     dreal_expr expr=NULL;
//     if(v->type==INTNUM||v->type==FPNUM){
//         expr = dreal_mk_num_from_string(ctx, v->name.c_str());
//         val = ConvertToDouble(v->name);
//     }
//     else if(v->type == INT || v->type==FP){
//         expr = table->getX(v->ID);
//         treat = treat&table->getVal(v->ID, val);
//     }
//     else
//         errs()<<"getExpr error : v->type error\n";
//     return expr;
// }


void NonlinearVerify::dreal_mk_tobv_expr(dreal_context ctx, dreal_expr x, string name, unsigned num, vector<dreal_expr> &xbv){
    dreal_expr xt_val = dreal_mk_unbounded_int_var(ctx, (name+"/bvval").c_str());
    dreal_expr xt_ast = dreal_mk_ite(ctx, dreal_mk_geq(ctx, x, dreal_mk_num(ctx, 0)), 
                            dreal_mk_eq(ctx, xt_val, x), 
                            dreal_mk_eq(ctx, xt_val, dreal_mk_minus(ctx, dreal_mk_num(ctx, pow(2.0, num)), x)));
    dreal_assert(ctx, xt_ast);
    if(outMode==1){
        cerr<<"(assert ";
        dreal_print_expr(xt_ast);
        cerr<<")"<<endl;
    }
    dreal_expr *xt = new dreal_expr[num];

    for(unsigned i=0;i<num;i++){
        string bvname = name+"/bv"+ConvertToString(i);
        xbv.push_back(dreal_mk_int_var(ctx, bvname.c_str(), 0, 1));
        xt[i] = dreal_mk_times_2(ctx, xbv[i], dreal_mk_num(ctx, pow(2.0, i)));
    }

    dreal_expr ast = dreal_mk_eq(ctx, xt_val, dreal_mk_plus(ctx, xt, num));
    dreal_assert(ctx, ast);
    if(outMode==1){
        cerr<<"(assert ";
        dreal_print_expr(ast);
        cerr<<")"<<endl;
    }
    delete[] xt;

    return;
}

dreal_expr NonlinearVerify::dreal_mk_AND(dreal_context ctx, dreal_expr y, dreal_expr z, string yname, string zname, unsigned num){
    dreal_expr* xt = new dreal_expr[num];
    vector<dreal_expr> xl;
    vector<dreal_expr> xr;

    dreal_mk_tobv_expr(ctx, y, yname, num, xl);
    dreal_mk_tobv_expr(ctx, z, zname, num, xr);

    for(unsigned i=0; i<num; i++){
        xt[i] = dreal_mk_times_2(ctx, dreal_mk_times_2(ctx, xl[i], xr[i]), dreal_mk_num(ctx, pow(2.0, i)));
    }

    dreal_expr ast = dreal_mk_plus(ctx, xt, num);
    delete[] xt;
    return ast;
}

dreal_expr NonlinearVerify::dreal_mk_NAND(dreal_context ctx, dreal_expr y, dreal_expr z, string yname, string zname, unsigned num){
    dreal_expr* xt = new dreal_expr[num];
    vector<dreal_expr> xl;
    vector<dreal_expr> xr;

    dreal_mk_tobv_expr(ctx, y, yname, num, xl);
    dreal_mk_tobv_expr(ctx, z, zname, num, xr);

    for(unsigned i=0; i<num; i++){
        xt[i] = dreal_mk_times_2(ctx, dreal_mk_minus(ctx, dreal_mk_num(ctx, 1), dreal_mk_times_2(ctx, xl[i], xr[i])), dreal_mk_num(ctx, pow(2.0, i)));
    }

    dreal_expr ast = dreal_mk_plus(ctx, xt, num);
    delete[] xt;
    return ast;
}

dreal_expr NonlinearVerify::dreal_mk_OR(dreal_context ctx, dreal_expr y, dreal_expr z, string yname, string zname, unsigned num){
    dreal_expr* xt = new dreal_expr[num];
    vector<dreal_expr> xl;
    vector<dreal_expr> xr;

    dreal_mk_tobv_expr(ctx, y, yname, num, xl);
    dreal_mk_tobv_expr(ctx, z, zname, num, xr);

    for(unsigned i=0; i<num; i++){
        dreal_expr xl_t = dreal_mk_minus(ctx, dreal_mk_num(ctx, 1), xl[i]);
        dreal_expr xr_t = dreal_mk_minus(ctx, dreal_mk_num(ctx, 1), xr[i]);
        xt[i] = dreal_mk_times_2(ctx, dreal_mk_minus(ctx, dreal_mk_num(ctx, 1), dreal_mk_times_2(ctx, xl_t, xr_t)), dreal_mk_num(ctx, pow(2.0, i)));
    }

    dreal_expr ast = dreal_mk_plus(ctx, xt, num);
    delete[] xt;
    return ast;
}

dreal_expr NonlinearVerify::dreal_mk_XOR(dreal_context ctx, dreal_expr y, dreal_expr z, string yname, string zname, unsigned num){
    dreal_expr* xt = new dreal_expr[num];
    vector<dreal_expr> xl;
    vector<dreal_expr> xr;

    dreal_mk_tobv_expr(ctx, y, yname, num, xl);
    dreal_mk_tobv_expr(ctx, z, zname, num, xr);

    for(unsigned i=0; i<num; i++){
        dreal_expr ite = dreal_mk_ite(ctx, dreal_mk_eq(ctx, xl[i], xr[i]), dreal_mk_num(ctx, 0), dreal_mk_num(ctx, 1));
        xt[i] = dreal_mk_times_2(ctx, ite, dreal_mk_num(ctx, pow(2.0, i)));
    }

    dreal_expr ast = dreal_mk_plus(ctx, xt, num);
    delete[] xt;
    return ast;
}

dreal_expr NonlinearVerify::dreal_mk_REM(dreal_context ctx, dreal_expr y, dreal_expr z, string name){
    string div_name = name+"/div";
    string real_name = name+"/divreal";
    dreal_expr div_real = dreal_mk_unbounded_real_var(ctx, real_name.c_str());
    dreal_expr div_expr = dreal_mk_unbounded_int_var(ctx, div_name.c_str());
    dreal_expr ast_t = dreal_mk_eq(ctx, div_real, dreal_mk_div(ctx, y, z));
    dreal_assert(ctx, ast_t);
    if(outMode==1){
        cerr<<"(assert ";
        dreal_print_expr(ast_t);
        cerr<<")"<<endl;
    }

    dreal_expr ast_tleq = dreal_mk_leq(ctx, div_expr, div_real);
    dreal_expr ast_tgt = dreal_mk_gt(ctx, div_expr, dreal_mk_minus(ctx, div_real, dreal_mk_num(ctx, 1)));
    dreal_expr ast_and = dreal_mk_and_2(ctx, ast_tleq, ast_tgt);
    dreal_assert(ctx, ast_and);
    if(outMode==1){
        cerr<<"(assert ";
        dreal_print_expr(ast_and);
        cerr<<")"<<endl;
    }

    dreal_expr ast = dreal_mk_minus(ctx, y, dreal_mk_times_2(ctx, div_expr, z));
    return ast;
}

dreal_expr NonlinearVerify::dreal_mk_ASHR(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num){
    dreal_expr* xt = new dreal_expr[num];
    vector<dreal_expr> x;

    dreal_mk_tobv_expr(ctx, y, name, num, x);


    for(unsigned i=0; i<num-rr; i++){
        xt[i] = dreal_mk_times_2(ctx, x[i+rr], dreal_mk_num(ctx, pow(2.0, i)));
    }
    for(unsigned i=num-rr; i<num; i++){
        xt[i] = dreal_mk_times_2(ctx, x[num-1], dreal_mk_num(ctx, pow(2.0, i)));
    }

    dreal_expr ast = dreal_mk_plus(ctx, xt, num);
    delete[] xt;
    return ast;
}

dreal_expr NonlinearVerify::dreal_mk_LSHR(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num){
    dreal_expr* xt = new dreal_expr[num];
    vector<dreal_expr> x;

    dreal_mk_tobv_expr(ctx, y, name, num, x);


    for(unsigned i=0; i<num-rr; i++){
        xt[i] = dreal_mk_times_2(ctx, x[i+rr], dreal_mk_num(ctx, pow(2.0, i)));
    }
    for(unsigned i=num-rr; i<num; i++){
        xt[i] = dreal_mk_num(ctx, 0);
    }

    dreal_expr ast = dreal_mk_plus(ctx, xt, num);
    delete[] xt;
    return ast;
}

dreal_expr NonlinearVerify::dreal_mk_SHL(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num){
    dreal_expr* xt = new dreal_expr[num];
    vector<dreal_expr> x;

    dreal_mk_tobv_expr(ctx, y, name, num, x);


    for(unsigned i=0; (int)i<rr; i++){
        xt[i] = dreal_mk_num(ctx, 0);
    }
    for(unsigned i=rr; i<num; i++){
        xt[i] = dreal_mk_times_2(ctx, x[i-rr], dreal_mk_num(ctx, pow(2.0, i)));
    }

    dreal_expr ast = dreal_mk_plus(ctx, xt, num);
    delete[] xt;
    return ast;
}

int NonlinearVerify::getCMP(int rl, int rr, Op_m pvop){
    bool cmp;
    switch(pvop){
        case slt:case ult:case flt: cmp = (rl<rr);break;
        case sle:case ule:case fle: cmp = (rl<=rr);break;
        case sgt:case ugt:case fgt: cmp = (rl>rr);break;
        case sge:case uge:case fge: cmp = (rl>=rr);break;
        case eq:case feq:   cmp = (rl==rr);break;
        case ne:case fne:   cmp = (rl!=rr);break;
        default:errs()<<"NonlinearVerify::getCMP error\n";
    }
    if(cmp)
        return 1;
    return 0;
}

///////////////////////////////////////BRICK-test////////////////////////////////////////////////////////////////////
dreal_expr NonlinearVerify::getExpr(Variable *v, bool &treat, double &val, NonlinearVarTable *table){

    dreal_expr Expr= NULL;

    if(v->type==FPNUM||v->type==INTNUM){

        val = v->getVal();
        string valstr = double2string(val);
        Expr = dreal_mk_num_from_string(ctx, valstr.c_str());
    }
    else if(v->type == INT || v->type==FP){
        Expr = table->getX(v->ID);
        treat = treat&table->getVal(v->ID, val);
    }
    else
        assert(false && "GetExpr error : v->type error!!");
    return Expr;
}


// generate the dreal_ast of compare constraint()
dreal_expr NonlinearVerify::mk_compare_ast(Constraint *con, NonlinearVarTable *table){
    dreal_expr exprl = NULL; 
    dreal_expr exprr = NULL;
    dreal_expr ast = NULL; 
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
        exprl = dreal_mk_num(ctx, (int)lval);
        exprr = dreal_mk_num(ctx, (int)rval);
    }
    else{
        bool treat = false;
        exprl = getExpr(lv, treat, lval, table);
        exprr = getExpr(rv, treat, rval, table);
    }

    switch(op){
        case EQ:case FEQ:    ast = dreal_mk_eq(ctx, exprl, exprr);break;
        case NE:case FNE:    ast = dreal_mk_not(ctx, dreal_mk_eq(ctx, exprl, exprr));break;
        case SLT:case ULT:case FLT:   ast = dreal_mk_lt(ctx, exprl, exprr);break;
        case SLE:case ULE:case FLE:   ast = dreal_mk_leq(ctx, exprl, exprr);break;
        case SGT:case UGT:case FGT:   ast = dreal_mk_gt(ctx, exprl, exprr);break;
        case SGE:case UGE:case FGE:   ast = dreal_mk_geq(ctx, exprl, exprr);break;
        default:    assert(false && "Operator type error!!");break;
    }

    return ast;
}

dreal_expr NonlinearVerify::mk_assignment_ast(Constraint *con, NonlinearVarTable *table, int time){
    
    dreal_expr ast=NULL; 
    // dreal_expr exprl; 
    dreal_expr exprr = NULL;

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
            //     table->setX(lv->ID, time, lv->type);
            // exprl = table->getX(lv->ID);

            Variable *rv = table->getAlias(rpv.rvar);

            if(rv->type==INTNUM||rv->type==FPNUM){

                bool treat = true;
                double val = 0;
                exprr = getExpr(rv, treat, val, table);

                table->setVal(lv->ID, val);
                table->setX(lv->ID, exprr);
                ast = NULL;

                // ast = dreal_mk_eq(ctx, exprl, exprr);
            }
            else{

                // exprr = table->getX(rv->ID);
                table->setAlias(lv->ID, rv->ID);
                double val = 0;

                if(table->getVal(rv->ID, val))
                    table->setVal(lv->ID, val);

                ast = NULL;
            }
        }
        else{

            // if(time>0)
            //     table->setX(lv->ID, time, lv->type);
            // exprl = table->getX(lv->ID);

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
                    ast = NULL;
                    // exprr = table->getX(rr);
                    // ast = dreal_mk_eq(ctx, exprl, exprr);

                    break;
                }
                case TRUNC:case ZEXT:case SEXT:case FPTRUNC:case FPEXT:case FPTOUI:case FPTOSI:case UITOFP:case SITOFP:case BITCAST:{
                    ast = mk_convert_expr(lv, rpv, table, time);
                    break;
                }
                case FADD:case ADD:case SUB:case FSUB:case MUL:case FMUL:case UDIV:case SDIV:case FDIV:
                case UREM:case SREM:case FREM:
                case LSHR:case ASHR:case SHL:case AND:case NAND:case OR:case XOR:{
                    ast = mk_binaryop_expr(lv, rpv, table, time);
                    break;
                }
                case ABS:case FABS:case SINH:case COSH:case TANH:case TAN:case ATAN:case ATAN2:
                case SIN:case ASIN:case COS:case ACOS:case SQRT:case POW:case LOG:case LOG10:case EXP:{
                    ast = mk_function_expr(lv, rpv, table, time);
                    break;
                }
                case ISNAN:case ISINF:case ISNORMAL:case ISFINITE:case SIGNBIT:case CLASSIFY:{
                    errs()<<"PVOP: "<<pvop<<"\n";
                    assert(false && "Mk_assignment_ast error: Can't handle floating-point with unlinear constraints!!");
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
                    assert(false && "Mk_assignment_ast LOAD error: Op_m is not a unlinear operator!!");
                    break;
            }
        }
    }
    
    return ast;
}

dreal_expr NonlinearVerify::mk_ptr_operation_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time){
    Op_m pvop = rpv.op;
    dreal_expr Expr=NULL;
    switch(pvop){
        case ALLOCA:{
            //  a = alloca
            //  PTR     exprid
            //  a       allocaID(initial as -2)
            int allocaID = table->alloca();
            table->setVal(lv->ID, allocaID);
            break;
        }
        case LOAD:{
            //  a = Load b
            //  PTR     exprid
            //  b       allocaID
            ///////////////////////////////
            //  expr    alias
            //  a       allocaID
            Variable *rv = table->getAlias(rpv.rvar);
            double val = 0;
            if(!table->getVal(rv->ID, val)){
                // errs()<<"0.LOAD GetVal error "<<rv->ID<<"\t"<<cfg->variableList[rv->ID].name<<"\n";
                assert(false && "Mk_ptr_operation_expr LOAD GetVal error!!");
            }  

            int allocaID = (int)val;

            int addr = table->load(allocaID);
            if(addr>=0){
                Variable *rvr = table->getAlias(addr);
                table->setAlias(lv->ID, rvr->ID);
            }
            break;
        }
        case STORE:{
            //  a = store b
            //  PTR     exprid
            //  a       b.exprid
            double val = 0;
            if(!table->getVal(lv->ID, val)){
                // errs()<<"Verifi store error "<<lv->ID<<"\t"<<lv->name<<"\n";
                assert(false && "Mk_ptr_operation_expr STORE GetVal error!!");
            }
            int allocaID = (int)val;

            Variable *rv = table->getAlias(rpv.rvar);
            
            if(rv->type!=PTR){
                dreal_expr exprr = table->getX(rv->ID);
                if(time>=0)
                    table->setX(rv->ID, time, rv->type);
                dreal_expr exprl = table->getX(rv->ID);
                Expr = dreal_mk_eq(ctx, exprl, exprr);
            }

            table->store(allocaID, rv->ID);

            break;
        }
        case ADDR:{
            //  a = addr b
            //  PTR     allocaID
            //  a       b.exprid
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
            //  c = a GETPTR a_0 a_1 a_2 .... e.g.
            //  c = a GETPTR 0 1 2
            //  PTR     PTR     PTR
            //  a   ->  a_0 
            //      ->  a_1 ->  a_1_0
            //              ->  a_1_1
            //              ->  a_1_2
            /////////////////////////////////////////
            //  PTR     alias
            //  c       a_1_2
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
        default:   
            assert(false && "Mk_ptr_operation_expr rpv.op error!!"); 
            break;
    }

    return Expr;
}

dreal_expr NonlinearVerify::mk_convert_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time){

    dreal_expr exprl = NULL; 

    Op_m pvop = rpv.op;
    
    if(time>0)
        table->setX(lv->ID, time, lv->type);
    exprl = table->getX(lv->ID);

    Variable *rv = table->getAlias(rpv.rvar);

    bool treat = true;
    double rval = 0;
    dreal_expr rv_expr = getExpr(rv, treat, rval, table);

    dreal_expr ast=NULL;
    switch(pvop){
        case TRUNC:{
            //truncate a large size bit-vector to a small size bit-vector
            assert(lv->type==INT && "Mk_convert_expr TRUNC error: lv is not integer type!!");
            assert(rv->type==INT && "Mk_convert_expr TRUNC error: rv is not integer type!!");
            assert(lv->numbits<rv->numbits && "Mk_convert_expr TRUNC error: lv numbits is larger than rv!!");

            table->setX(lv->ID, rv_expr);
            // ast = dreal_mk_eq(ctx, exprl, rv_expr);
            break;
        }
        case ZEXT:{
            //Extend small size bit-vector with zeros to large size bit-vector 
            assert(lv->type==INT && "Mk_convert_expr ZEXT error: lv is not integer type!!");
            assert(rv->type==INT && "Mk_convert_expr ZEXT error: rv is not integer type!!");
            assert(lv->numbits>rv->numbits && "Mk_convert_expr ZEXT error: lv numbits is smaller than rv!!");

            table->setX(lv->ID, rv_expr);
            // ast = dreal_mk_eq(ctx, exprl, rv_expr);
            break;
        }
        case SEXT:{
            //Extend small size bit-vector with sign bit to large size bit-vector 
            assert(lv->type==INT && "Mk_convert_expr SEXT error: lv is not integer type!!");
            assert(rv->type==INT && "Mk_convert_expr SEXT error: rv is not integer type!!");
            assert(lv->numbits>rv->numbits && "Mk_convert_expr SEXT error: lv numbits is smaller than rv!!");

            table->setX(lv->ID, rv_expr);
            // ast = dreal_mk_eq(ctx, exprl, rv_expr);
            break;
        }
        case FPTRUNC:{
            //truncate a large size float point type to a small size float point type
            //i.e. convert double to float now
            assert((lv->type==FP && lv->numbits==32) && "Mk_convert_expr FPTRUNC error: lv is not float type!!");
            assert((rv->type==FP && rv->numbits==64) && "Mk_convert_expr FPTRUNC error: rv is not double type!!");
            assert(lv->numbits<rv->numbits && "Mk_convert_expr FPTRUNC error: lv numbits is larger than rv!!");
            
            table->setX(lv->ID, rv_expr);
            // ast = dreal_mk_eq(ctx, exprl, rv_expr);
            break;
        }
        case FPEXT:{
            //extend a small size float point  type to a large size float point type
            //i.e. convert float to double now
            assert((lv->type==FP && lv->numbits==64) && "Mk_convert_expr FPEXT error: lv is not double type!!");
            assert((rv->type==FP && rv->numbits==32) && "Mk_convert_expr FPEXT error: rv is not float type!!");
            assert(lv->numbits>rv->numbits && "Mk_convert_expr FPEXT error: lv numbits is smaller than rv!!");
            
            table->setX(lv->ID, rv_expr);
            // ast = dreal_mk_eq(ctx, exprl, rv_expr);
            break;
        }
        case FPTOUI:{
            //Conversion of a floating-point term into an unsigned bit-vector.
            assert(lv->type==INT && "Mk_convert_expr FPTOUI error: lv is not integer type!!");
            assert(rv->type==FP && "Mk_convert_expr FPTOUI error: rv is not float type!!");

            dreal_expr exprl_t = dreal_mk_unbounded_int_var(ctx, (lv->name+"/t").c_str());
            dreal_expr ast_tleq_pos = dreal_mk_leq(ctx, exprl, rv_expr);
            dreal_expr ast_tgt_pos = dreal_mk_gt(ctx, exprl, dreal_mk_minus(ctx, rv_expr, dreal_mk_num(ctx, 1)));
            dreal_expr ast_and_pos = dreal_mk_and_2(ctx, ast_tleq_pos, ast_tgt_pos);
            dreal_expr ast_tgeq_neg = dreal_mk_geq(ctx, exprl_t, rv_expr);
            dreal_expr ast_tlt_neg = dreal_mk_gt(ctx, exprl_t, dreal_mk_plus_2(ctx, rv_expr, dreal_mk_num(ctx, 1)));
            dreal_expr ast_assign_neg = dreal_mk_eq(ctx, exprl, dreal_mk_minus(ctx, dreal_mk_num(ctx, pow(2.0, lv->numbits)), exprl_t));
            dreal_expr ast_and_neg = dreal_mk_and_3(ctx, ast_tgeq_neg, ast_tlt_neg, ast_assign_neg);

            ast = dreal_mk_ite(ctx, dreal_mk_leq(ctx, rv_expr, dreal_mk_num(ctx, 0)), ast_and_neg, ast_and_pos);
            rval = (unsigned)rval;
            // assert(false && "Mk_convert_expr FPTOUI error: FPTOUI can't handle with unlinear constraints yet!!");
            break;
        }
        case FPTOSI:{
            //Conversion of a floating-point term into a signed bit-vector.
            assert(lv->type==INT && "Mk_convert_expr FPTOSI error: lv is not integer type!!");
            assert(rv->type==FP && "Mk_convert_expr FPTOSI error: rv is not float type!!");

            
            dreal_expr ast_tleq_pos = dreal_mk_leq(ctx, exprl, rv_expr);
            dreal_expr ast_tgt_pos = dreal_mk_gt(ctx, exprl, dreal_mk_minus(ctx, rv_expr, dreal_mk_num(ctx, 1)));
            dreal_expr ast_and_pos = dreal_mk_and_2(ctx, ast_tleq_pos, ast_tgt_pos);
            dreal_expr ast_tgeq_neg = dreal_mk_geq(ctx, exprl, rv_expr);
            dreal_expr ast_tlt_neg = dreal_mk_gt(ctx, exprl, dreal_mk_plus_2(ctx, rv_expr, dreal_mk_num(ctx, 1)));
            dreal_expr ast_and_neg = dreal_mk_and_2(ctx, ast_tgeq_neg, ast_tlt_neg);

            ast = dreal_mk_ite(ctx, dreal_mk_leq(ctx, rv_expr, dreal_mk_num(ctx, 0)), ast_and_neg, ast_and_pos);
            rval = (int)rval;
            break;
        }
        case UITOFP:{
            //Conversion of a 2's complement unsigned bit-vector term into a term of Float Point sort.
            assert(lv->type==FP && "Mk_convert_expr UITOFP error: lv is not float type!!");
            assert(rv->type==INT && "Mk_convert_expr UITOFP error: rv is not integer type!!");

            table->setX(lv->ID, rv_expr);
            // ast = dreal_mk_eq(ctx, exprl, rv_expr);
            break;
        }
        case SITOFP:{
            //Conversion of a 2's complement signed bit-vector term into a term of Float Point sort.
            assert(lv->type==FP && "Mk_convert_expr SITOFP error: lv is not float type!!");
            assert(rv->type==INT && "Mk_convert_expr SITOFP error: rv is not integer type!!");

            table->setX(lv->ID, rv_expr);
            // ast = dreal_mk_eq(ctx, exprl, rv_expr);
            break;
        }
        case BITCAST:{
            assert(lv->numbits==rv->numbits && "Mk_convert_expr BITCAST error: Have different size type!!");

            assert(false && "Mk_convert_expr BITCAST error: Bitcast with Nonlinear constraints can't handle yet!!");
            break;
        }
        default:
            assert(false && "Mk_convert_expr error: Op_m is not a conversion Operator!!");
            break;
    }

    if(treat)
        table->setVal(lv->ID, rval);

    return ast;
}

dreal_expr NonlinearVerify::mk_binaryop_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time){

    // dreal_expr exprl; 
    dreal_expr exprr = NULL;
    assert(rpv.isExp && "Mk_binaryop_expr error: rpv is not a expression!!");

    Op_m pvop = rpv.op;
    
    // if(time>0)
    //     table->setX(lv->ID, time, lv->type);
    // exprl = table->getX(lv->ID);

    Variable *rvl = table->getAlias(rpv.lvar);
    Variable *rvr = table->getAlias(rpv.rvar);

    bool treat = true;
    double rvlval = 0;
    double rvrval = 0;
    double rval = 0;
    dreal_expr rvl_expr = getExpr(rvl, treat, rvlval, table);
    dreal_expr rvr_expr = getExpr(rvr, treat, rvrval, table);

    switch(pvop){
        case ADD:{
            assert(lv->type==INT && "Mk_binaryop_expr ADD error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr ADD error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr ADD error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr ADD error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_plus_2(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = (int)rvlval+(int)rvrval;
            break;
        }
        case SUB:{
            assert(lv->type==INT && "Mk_binaryop_expr SUB error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr SUB error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr SUB error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr SUB error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_minus(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = (int)rvlval-(int)rvrval;
            break;
        }
        case MUL:{
            assert(lv->type==INT && "Mk_binaryop_expr MUL error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr MUL error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr MUL error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr MUL error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_times_2(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = (int)rvlval*(int)rvrval;
            break;
        }
        case UDIV:{
            assert(lv->type==INT && "Mk_binaryop_expr UDIV error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr UDIV error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr UDIV error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr UDIV error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_div(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = (unsigned)rvlval/(unsigned)rvrval;
            break;
        }
        case SDIV:{
            assert(lv->type==INT && "Mk_binaryop_expr SDIV error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr SDIV error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr SDIV error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr SDIV error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_div(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = (int)rvlval/(int)rvrval;
            break;
        }
        case FADD:{
            assert(lv->type==FP && "Mk_binaryop_expr FADD error: lv is not a float point type!!");
            assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FADD error: rvl is not a float point type!!");
            assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FADD error: rvr is not a float point type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FADD error: rvl and rvr have different float point type!!");

            exprr = dreal_mk_plus_2(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = rvlval+rvrval;
            break;
        }
        case FSUB:{
            assert(lv->type==FP && "Mk_binaryop_expr FSUB error: lv is not a float point type!!");
            assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FSUB error: rvl is not a float point type!!");
            assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FSUB error: rvr is not a float point type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FSUB error: rvl and rvr have different float point type!!");

            exprr = dreal_mk_minus(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = rvlval-rvrval;
            break;
        }
        case FMUL:{
            assert(lv->type==FP && "Mk_binaryop_expr FMUl error: lv is not a float point type!!");
            assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FMUl error: rvl is not a float point type!!");
            assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FMUl error: rvr is not a float point type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FMUl error: rvl and rvr have different float point type!!");

            exprr = dreal_mk_times_2(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = rvlval*rvrval;
            break;
        }
        case FDIV:{
            assert(lv->type==FP && "Mk_binaryop_expr FDIV error: lv is not a float point type!!");
            assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FDIV error: rvl is not a float point type!!");
            assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FDIV error: rvr is not a float point type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FDIV error: rvl and rvr have different float point type!!");

            exprr = dreal_mk_div(ctx, rvl_expr, rvr_expr);

            if(treat)
                rval = rvlval/rvrval;
            break;
        }
        case UREM:{
            assert(lv->type==INT && "Mk_binaryop_expr UREM error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr UREM error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr UREM error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr UREM error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_REM(ctx, rvl_expr, rvr_expr, lv->name);

            if(treat)
                rval = (unsigned)rvlval%(unsigned)rvrval;
            break;
        }
        case SREM:{
            assert(lv->type==INT && "Mk_binaryop_expr SREM error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr SREM error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr SREM error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr SREM error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_REM(ctx, rvl_expr, rvr_expr, lv->name);

            if(treat)
                rval = (int)rvlval%(int)rvrval;
            break;
        }
        case FREM:{
            assert(lv->type==FP && "Mk_binaryop_expr FREM error: lv is not a float point type!!");
            assert((rvl->type==FP||rvl->type==FPNUM) && "Mk_binaryop_expr FREM error: rvl is not a float point type!!");
            assert((rvr->type==FP||rvr->type==FPNUM) && "Mk_binaryop_expr FREM error: rvr is not a float point type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr FREM error: rvl and rvr have different float point type!!");

            exprr = dreal_mk_REM(ctx, rvl_expr, rvr_expr, lv->name);

            treat = false;
            break;
        }
        case LSHR:{
            assert(lv->type==INT && "Mk_binaryop_expr LSHR error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr LSHR error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr LSHR error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr LSHR error: rvl and rvr have different interger type!!");

            if(!treat)
                assert(false && "Mk_binaryop_expr LSHR error: can't handle LSHR with unlinear constraints!!");
            exprr = dreal_mk_LSHR(ctx, rvl_expr, (int)rvrval, rvl->name, rvl->numbits);
            treat = false;
            break;
        }
        case ASHR:{
            assert(lv->type==INT && "Mk_binaryop_expr ASHR error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr ASHR error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr ASHR error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr ASHR error: rvl and rvr have different interger type!!");

            if(!treat)
                assert(false && "Mk_binaryop_expr ASHR error: can't handle ASHR with unlinear constraints!!");
            exprr = dreal_mk_ASHR(ctx, rvl_expr, (int)rvrval, rvl->name, rvl->numbits);
            treat = false;
            break;
        }
        case SHL:{
            assert(lv->type==INT && "Mk_binaryop_expr SHL error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr SHL error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr SHL error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr SHL error: rvl and rvr have different interger type!!");

            
            if(!treat)
                assert(false && "Mk_binaryop_expr SHL error: can't handle SHL with unlinear constraints!!");
            exprr = dreal_mk_SHL(ctx, rvl_expr, (int)rvrval, rvl->name, rvl->numbits);
            treat = false;
            break;
        }
        case AND:{
            assert(lv->type==INT && "Mk_binaryop_expr AND error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr AND error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr AND error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr AND error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_AND(ctx, rvl_expr, rvr_expr, rvl->name, rvr->name, rvl->numbits);
            treat = false;
            break;
        }
        case NAND:{
            assert(lv->type==INT && "Mk_binaryop_expr NAND error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr NAND error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr NAND error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr NAND error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_NAND(ctx, rvl_expr, rvr_expr, rvl->name, rvr->name, rvl->numbits);
            treat = false;
            break;
        }
        case OR:{
            assert(lv->type==INT && "Mk_binaryop_expr OR error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr OR error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr OR error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr OR error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_OR(ctx, rvl_expr, rvr_expr, rvl->name, rvr->name, rvl->numbits);
            treat = false;
            break;
        }
        case XOR:{
            assert(lv->type==INT && "Mk_binaryop_expr XOR error: lv is not a interger type!!");
            assert((rvl->type==INT||rvl->type==INTNUM) && "Mk_binaryop_expr XOR error: rvl is not a interger type!!");
            assert((rvr->type==INT||rvr->type==INTNUM) && "Mk_binaryop_expr XOR error: rvr is not a interger type!!");
            assert(rvl->numbits==rvr->numbits && "Mk_binaryop_expr XOR error: rvl and rvr have different interger type!!");

            exprr = dreal_mk_XOR(ctx, rvl_expr, rvr_expr, rvl->name, rvr->name, rvl->numbits);
            treat = false;
            break;
        }
        default:
            assert(false && "Mk_binaryop_expr error: Op_m is not a binary operator!!");
            break;
    }

    if(treat)
        table->setVal(lv->ID, rval);

    table->setX(lv->ID, exprr);
    return NULL;
    // return dreal_mk_eq(ctx, exprl, exprr);
}


dreal_expr NonlinearVerify::mk_compare_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time){
    assert(rpv.isExp && "Mk_compare_expr error: rpv is not a expression!!");

    assert((lv->type==INT&&lv->numbits==1) && "Mk_compare_expr error: lv is not a i1 type!!");

    Op_m pvop = rpv.op;
    
    if(time>0)
        table->setX(lv->ID, time, lv->type);
    dreal_expr exprl = table->getX(lv->ID);

    Variable *rvl = table->getAlias(rpv.lvar);
    Variable *rvr = table->getAlias(rpv.rvar);
    bool treat = true;
    double rvlval = 0;
    double rvrval = 0;
    double rval = 0;
    dreal_expr y = getExpr(rvl, treat, rvlval, table);
    dreal_expr z = getExpr(rvr, treat, rvrval, table);
    dreal_expr cmp = NULL;
    switch(pvop){
        case slt:case ult:case flt:
            cmp = dreal_mk_lt(ctx, y, z);break;
        case sle:case ule:case fle:
            cmp = dreal_mk_leq(ctx, y, z);break;
        case sgt:case ugt:case fgt:
            cmp = dreal_mk_gt(ctx, y, z);break;
        case sge:case uge:case fge:
            cmp = dreal_mk_geq(ctx, y, z);break;
        case eq:case feq:
            cmp = dreal_mk_eq(ctx, y, z);break;
        case ne:case fne:
            cmp = dreal_mk_not(ctx, dreal_mk_eq(ctx, y, z));break;
        default:errs()<<"NonlinearVerify::dreal_mk_INT_cmp error\n";
    }
    
    if(treat){
        rval = getCMP(rvlval, rvrval, pvop);
        table->setVal(lv->ID, rval);
    }

    dreal_expr ite_expr = dreal_mk_ite(ctx, cmp, dreal_mk_num(ctx, 1), dreal_mk_num(ctx, 0));
    table->setX(lv->ID, ite_expr);
    return NULL;
    // dreal_expr assign = dreal_mk_ite(ctx, cmp, 
    //                                 dreal_mk_eq(ctx, exprl, dreal_mk_num(ctx, 1)),
    //                                  dreal_mk_eq(ctx, exprl, dreal_mk_num(ctx, 0)));

    // dreal_expr assign = dreal_mk_eq(ctx, exprl, dreal_mk_ite(ctx, cmp, 
    //                                                 dreal_mk_num(ctx, 1),
    //                                                     dreal_mk_num(ctx, 0)));
    
    // return assign;
}

dreal_expr NonlinearVerify::mk_function_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time){
    // dreal_expr exprl;
    dreal_expr exprr = NULL;
    assert(rpv.isExp && "Mk_compare_expr error: rpv is not a expression!!");

    Op_m pvop = rpv.op;
    
    // if(time>0)
    //     table->setX(lv->ID, time, lv->type);
    // exprl = table->getX(lv->ID);

    Variable *rv = table->getAlias(rpv.rvar);


    bool treat = true;
    double rval = 0;
    dreal_expr rv_expr = getExpr(rv, treat, rval, table);

    switch(pvop){
        case ABS:{
            assert(rv->type==INT||rv->type==INTNUM && "Mk_function_expr ABS error: rv is not an integer type!!");
            exprr = dreal_mk_abs(ctx, rv_expr);
            break;
        }
        case FABS:{
            assert(rv->type==FP||rv->type==FPNUM && "Mk_function_expr FABS error: rv is not a float point type!!");
            exprr = dreal_mk_abs(ctx, rv_expr);
            break;
        }
        case ISNAN:{
            assert(rv->type==FP||rv->type==FPNUM && "Mk_function_expr ISNAN error: rv is not a float point type!!");
            assert(false && "Mk_function_expr ISNAN error: Can't handle isnan with unlinear constraints!!");
            break;
        }
        case ISINF:{
            assert(rv->type==FP||rv->type==FPNUM && "Mk_function_expr ISINF error: rv is not a float point type!!");
            assert(false && "Mk_function_expr ISINF error: Can't handle isinf with unlinear constraints!!");
            break;
        }
        case ISNORMAL:{
            assert(rv->type==FP||rv->type==FPNUM && "Mk_function_expr ISNORMAL error: rv is not a float point type!!");
            assert(false && "Mk_function_expr ISNORMAL error: Can't handle isnormal with unlinear constraints!!");
            break;
        }
        case ISFINITE:{
            assert(rv->type==FP||rv->type==FPNUM && "Mk_function_expr ISFINITE error: rv is not a float point type!!");
            assert(false && "Mk_function_expr ISFINITE error: Can't handle isfinite with unlinear constraints!!");
            break;
        }
        case SIGNBIT:{
            assert(rv->type==FP||rv->type==FPNUM && "Mk_function_expr SIGNBIT error: rv is not an integer type!!");
            dreal_expr is_negative = dreal_mk_lt(ctx, rv_expr, dreal_mk_num(ctx, 0));
            exprr = dreal_mk_ite(ctx, is_negative, dreal_mk_num(ctx, 1), dreal_mk_num(ctx, 0));
            break;
        }
        case CLASSIFY:{
            assert(rv->type==FP||rv->type==FPNUM && "Mk_function_expr CLASSIFY error: rv is not an integer type!!");
            assert(false && "Mk_function_expr CLASSIFY error: Can't handle classify with unlinear constraints!!");
            break;
        }
        case SINH:{
            exprr = dreal_mk_sinh(ctx, rv_expr);
            break;
        }
        case COSH:{
            exprr = dreal_mk_cosh(ctx, rv_expr);
            break;
        }
        case TANH:{
            exprr = dreal_mk_tanh(ctx, rv_expr);
            break;
        }
        case TAN:{
            exprr = dreal_mk_tan(ctx, rv_expr);
            break;
        }
        case ATAN:{
            exprr = dreal_mk_atan(ctx, rv_expr);
            break;
        }
        case ATAN2:{
            rv = table->getAlias(rpv.lvar);
            dreal_expr rvl_expr = getExpr(rv, treat, rval, table);
            exprr = dreal_mk_atan2(ctx, rvl_expr, rv_expr);
            break;
        }
        case SIN:{
            exprr = dreal_mk_sin(ctx, rv_expr);
            break;
        }
        case ASIN:{
            exprr = dreal_mk_asin(ctx, rv_expr);
            break;
        }
        case COS:{
            exprr = dreal_mk_cos(ctx, rv_expr);
            break;
        }
        case ACOS:{
            exprr = dreal_mk_acos(ctx, rv_expr);
            break;
        }
        case SQRT:{
            exprr = dreal_mk_pow(ctx, rv_expr, dreal_mk_num(ctx, 0.5));
            break;
        }
        case POW:{
            rv = table->getAlias(rpv.lvar);
            dreal_expr rvl_expr = getExpr(rv, treat, rval, table);
            exprr = dreal_mk_pow(ctx, rvl_expr, rv_expr);
            break;
        }
        case LOG:{
            exprr = dreal_mk_log(ctx, rv_expr);
            break;
        }
        case LOG10:{
            exprr = dreal_mk_div(ctx, dreal_mk_log(ctx, rv_expr),dreal_mk_log(ctx, dreal_mk_num(ctx, 10)));
            break;
        }
        case EXP:{
            exprr = dreal_mk_exp(ctx, rv_expr);
            break;
        }
        default:
            assert(false && "Mk_function_expr error: Op_m is not a function operator!!");
            break;
    }

    table->setX(lv->ID, exprr);
    return NULL;
    // return dreal_mk_eq(ctx, exprl, exprr);
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

dreal_expr NonlinearVerify::tran_constraint(Constraint *con, NonlinearVarTable *table, int time)
{
    dbg->getConsInfo(con);
    Operator op = con->op;

    dreal_expr ast=NULL; 

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
        }
        default:
            assert(false && "Tran_constraint error: Unvalid operator!!");
            break;
    }

    return ast;

/* 
    dreal_expr exprl; 
    dreal_expr exprr;
    dreal_expr ast; 

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
                exprl = dreal_mk_num(ctx, lval);
                exprr = dreal_mk_num(ctx, rval);
            }
            else{
                if(lv->type==INTNUM||lv->type==FPNUM){
                    exprl = dreal_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==INTNUM||rv->type==FPNUM){
                    exprr = dreal_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = dreal_mk_lt(ctx, exprl, exprr);
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
                exprl = dreal_mk_num(ctx, lval);
                exprr = dreal_mk_num(ctx, rval);
            }
            else{
                if(lv->type==INTNUM||lv->type==FPNUM){
                    exprl = dreal_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==INTNUM||rv->type==FPNUM){
                    exprr = dreal_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = dreal_mk_leq(ctx, exprl, exprr);
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
                exprl = dreal_mk_num(ctx, lval);
                exprr = dreal_mk_num(ctx, rval);
            }
            else{
                if(lv->type==INTNUM||lv->type==FPNUM){
                    exprl = dreal_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==INTNUM||rv->type==FPNUM){
                    exprr = dreal_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = dreal_mk_gt(ctx, exprl, exprr);
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
                exprl = dreal_mk_num(ctx, lval);
                exprr = dreal_mk_num(ctx, rval);
            }
            else{
                if(lv->type==INTNUM||lv->type==FPNUM){
                    exprl = dreal_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==INTNUM||rv->type==FPNUM){
                    exprr = dreal_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = dreal_mk_geq(ctx, exprl, exprr);
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
                exprl = dreal_mk_num(ctx, lval);
                exprr = dreal_mk_num(ctx, rval);
            }
            else{
                if(lv->type==INTNUM||lv->type==FPNUM){
                    exprl = dreal_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==INTNUM||rv->type==FPNUM){
                    exprr = dreal_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = dreal_mk_eq(ctx, exprl, exprr);
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
                exprl = dreal_mk_num(ctx, lval);
                exprr = dreal_mk_num(ctx, rval);
            }
            else{
                if(lv->type==INTNUM||lv->type==FPNUM){
                    exprl = dreal_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==INTNUM||rv->type==FPNUM){
                    exprr = dreal_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }        
            ast = dreal_mk_not(ctx, dreal_mk_eq(ctx, exprl, exprr));
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
                    Variable *rvr;
                    double rvrval,val;
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
                return NULL;
            }
            else if(lv->type==INT||lv->type==FP){
                if(time>1)
                    table->setX(lv->ID, time, lv->type);
                exprl = table->getX(lv->ID);

                if(!rpv.isExp){
                    rv = table->getAlias(rpv.rvar);
                    if(rv->type==INTNUM||rv->type==FPNUM){
                        exprr = dreal_mk_num_from_string(ctx, rv->name.c_str());
                        double val = ConvertToDouble(rv->name);
                        table->setVal(lv->ID, val);
                    }
                    else if(rv->type==INT || rv->type==FP){
                        exprr = table->getX(rv->ID);
                        double val;
                        if(lv->type==INT && rv->type==FP){
                            dreal_expr ast_tleq = dreal_mk_leq(ctx, exprl, exprr);
                            dreal_expr ast_tgt = dreal_mk_gt(ctx, exprl, dreal_mk_minus(ctx, exprr, dreal_mk_num(ctx, 1)));
                            dreal_expr ast_and = dreal_mk_and_2(ctx, ast_tleq, ast_tgt);
                            
                            if(table->getVal(rv->ID, val))
                                table->setVal(lv->ID, (int)val);
                            return ast_and;
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
                    Variable *rvl;
                    Variable *rvr;
                    double rl=0;
                    double rr=0;
                    double val=0;
                    dreal_expr y;
                    dreal_expr z;
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
                            exprr = dreal_mk_AND(ctx, y, z, name, 32);    
                            if(treat)
                                table->setVal(lv->ID, (int)rl&(int)rr);
                            break;
                        case NAND:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_NAND(ctx, y, z, name, 32);
                            if(treat)
                                table->setVal(lv->ID, ~((int)rl&(int)rr));
                            break;
                        case OR:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_OR(ctx, y, z, name, 32);
                            if(treat)
                                table->setVal(lv->ID, (int)rl|(int)rr);
                            break;
                        case XOR:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_XOR(ctx, y, z, name, 32);
                            if(treat)
                                table->setVal(lv->ID, (int)rl^(int)rr);
                            break;
                        case SREM:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_SREM(ctx, y, z, name);
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
                            if(rr<0)
                                exprr = dreal_mk_SHL(ctx, y, -(int)rr, name, 32);
                            else
                                exprr = dreal_mk_ASHR(ctx, y, (int)rr, name, 32);
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
                            if(rr>=0)
                                exprr = dreal_mk_SHL(ctx, y, (int)rr, name, 32);
                            else
                                exprr = dreal_mk_ASHR(ctx, y, -(int)rr, name, 32);
                            if(treat)
                                table->setVal(lv->ID, (int)rl<<(int)rr);
                            break;
                        case ADD:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_plus_2(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, rl+rr);
                            break;
                        case SUB:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_minus(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, rl-rr);
                            break;
                        case TAN:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_tan(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, tan(rr));
                            break;
                        case ATAN:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_atan(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, atan(rr));
                            break;
                        case ATAN2:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_atan2(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, atan2(rl, rr));
                            break;
                        case SIN:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_sin(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, sin(rr));
                            break;
                        case ASIN:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_asin(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, asin(rr));
                            break;
                        case COS:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_cos(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, cos(rr));
                            break;
                        case ACOS:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_acos(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, acos(rr));
                            break;
                        case SQRT:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_pow(ctx, z, dreal_mk_num(ctx, 0.5));
                            if(treat)
                                table->setVal(lv->ID, sqrt(rr));
                            break;
                        case POW:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_pow(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, powf(rl,rr));
                            break;
                        case LOG:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_log(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, log(rr));
                            break;
                        case LOG10:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_div(ctx, dreal_mk_log(ctx, z),dreal_mk_log(ctx, dreal_mk_num(ctx, 10)));
                            if(treat)
                                table->setVal(lv->ID, log10(rr));
                            break;
                        case ABS:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_abs(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, fabs(rr));
                            break;
                        case EXP:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_exp(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, exp(rr));
                            break;
                        case SINH:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_sinh(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, sinh(rr));
                            break;
                        case COSH:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_cosh(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, cosh(rr));
                            break;
                        case TANH:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_tanh(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, tanh(rr));
                            break;
                        case MUL:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_times_2(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, rl*rr);
                            break;
                        case DIV:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_div(ctx, y, z);
                            if(treat&&rr!=0)
                                table->setVal(lv->ID, rl/rr);
                            break;
                        case lt:case le:case gt:case ge:case eq:case ne:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = dreal_mk_INT_cmp(ctx, y, z, pvop, name);
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
            ast = dreal_mk_eq(ctx, exprl, exprr);
            break;
        }
    }

    return ast;
    */          

}

void NonlinearVerify::get_constraint(vector<Constraint> &consList, NonlinearVarTable *table, int time, bool isTransition){
   
    /* 
    unsigned size = consList.size();
    
    bool isOR = (isTransition && size>1);
    dreal_expr *cons=NULL;
    if(isOR)
        cons = new dreal_expr[size];
    */

    for(unsigned m=0;m<consList.size();m++)
    {
        Constraint* con = &consList[m];
        // if(outMode==1)
        //     errs()<<*con<<"\n";
        dreal_expr ast = tran_constraint(con, table, time );
        if(ast!=NULL){

            // if(!total)
            //     total = ast;
            // else
            //     total = dreal_mk_and_2(ctx, total, ast);
            // dreal_push(ctx);
            // dreal_assert(ctx, ast);
            dreal::solver *sv = &s;
            s.add(dreal::expr(sv, ast));
            // s.print_problem();
            // dreal_result res = dreal_check( ctx );

            if(outMode==1){
                cerr<<"(assert ";
                dreal_print_expr(ast);
                cerr<<")"<<endl;
            }

            // if(res == l_true){
            //     cerr<<"sat\n";
            // }
            // else{
            //     cerr<<"unsat\n";
            // }
        } 
        else{
            if(outMode==1){
                //cerr<<"......"<<"\n";
            }
        }

    }
/*
    if(isOR){
        dreal_expr exprs = dreal_mk_or(ctx, cons, size);
        dreal_print_expr(exprs);
        dreal_assert(ctx, exprs);
        cerr<< endl;
    }
*/
}

void NonlinearVerify::encode_path(CFG* ha, vector<int> &patharray)
{
    table = new NonlinearVarTable(ctx, ha);

    int state_num = 0;
    if(patharray.size()%2)
        state_num = (patharray.size()+1)/2;
    else
        state_num = patharray.size()/2;
    int total_state  = ha->stateList.size()+ ha->transitionList.size();
    vector<int> repeat(total_state,0);
    
    for (int j= 0;j<state_num; j++)
    {    
        int ID = patharray[2*j];
        State* st=ha->searchState(ID);
        assert(st!=NULL);
        if(outMode==1)
            cerr<<st->name<<":"<<endl;
        get_constraint(st->consList, table, repeat[ID], false);
        repeat[ID]+=1;
        
        // if(j!=state_num-1) 
        if(2*j+1<patharray.size())   
        {
            ID = patharray[2*j+1];
            Transition* pre=ha->searchTransition(ID);
            assert(pre!=NULL);
            if(outMode==1)
                cerr<<pre->name<<":"<<endl;

            get_constraint(pre->guardList, table, repeat[ID], true);    
            repeat[ID]+=1;

        }
    }
//    cerr<<"Path encode complete~~~~~~~~~~~~~~~~~~ "<<endl;
    // table->printAliasMap();
    // dreal_result res = dreal_check( ctx );

    // if(res == l_true){
    //     errs()<<"sat\n";
    // }
    // else{
    //     errs()<<"unsat\n";
    // }
}

bool NonlinearVerify::analyze_unsat_core(int state){
    // dreal_assert(ctx, total);
    // dreal_print_expr(total);
    // s.print_problem();
    dreal_result res = dreal_check( ctx );

    if(res==l_true){
        return true;
    }
    else{
        add_IIS(IndexPair(0, state));
        return false;
    }
}

void NonlinearVerify::add_IIS(IndexPair index){
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

void NonlinearVerify::clear(){
    index_cache.clear();
    core_index.clear();
    if(table)
        delete table;
    table = NULL;
    dreal_del_context(ctx);
    // dreal_reset(ctx);
    errs()<<"Del dreal_context\n";
    ctx = NULL;
    //dreal_del_context(ctx);
    // ctx = dreal_mk_context(qf_nra);
    // dreal_set_precision(ctx, precision);
}

void NonlinearVerify::reset(){
    index_cache.clear();
    core_index.clear();
    if(table)
        delete table;
    table = NULL;
    dreal_reset(ctx);
    errs()<<"Reset dreal_context\n";
    // dreal_del_context(ctx);
    dreal_init();
    ctx = dreal_mk_context(qf_nra);
    dreal_set_precision(ctx, precision);
}
