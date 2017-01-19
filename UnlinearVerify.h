#ifndef _unlinearverify_h
#define _unlinearverify_h
#include "CFG.h"
#include "general.h"
#include <stdio.h>
#include <cstdlib>
#include <sstream>
#include <cstring>
#include "dreal.h"
//#include "Solver.h"
//#include "dreal_c.h"
#include <fstream>
#include "math.h"
#include "DebugInfo.h"

extern int smt2set_in   (FILE *);
extern int smt2parse    ();
extern int m_argc;
extern char ** m_argv;

class UnlinearVarTable{
private:
    dreal_context &ctx;
    int var_num;
    int alloca_num;
    map<int, double> varVal;
    map<int, int>storeMap;
    map<int, int> alias;
    vector<dreal_expr> x;
    map<int, int> exprMap;
    CFG *cfg;
public:
    UnlinearVarTable(dreal_context &c, CFG *ha);

    ~UnlinearVarTable();

    void setX(int ID, int time, VarType type);
    int alloca();
    void setAlias(int ID1, int ID2);
    void setAlias(Variable *v1, Variable *v2);
    void setVal(int ID, double val);
    void store(int ID1, int ID2);
    int getNum();
    dreal_expr getX(int ID);
    int load(int ID);
    bool hasAlias(Variable *v);
    Variable* getAlias(int ID);

    Variable* getAlias(Variable* var);
    bool getVal(Variable *var, double &v);
    bool getVal(int ID, double &v);
    map<int, double> getValmap();
    map<int, int> getAliasmap();
    CFG *getCFG();
};

class UnlinearVerify: public Verify{

    string smt;
    dreal_context ctx;
    UnlinearVarTable *table;
    double time;
    double precision;
    int outMode;
    DebugInfo *dbg;

    dreal_expr getExpr(Variable *v, bool &treat, double &val, UnlinearVarTable *table);
    dreal_expr dreal_mk_AND(dreal_context ctx, dreal_expr y, dreal_expr z, string name, unsigned num);
    dreal_expr dreal_mk_NAND(dreal_context ctx, dreal_expr y, dreal_expr z, string name, unsigned num);
    dreal_expr dreal_mk_OR(dreal_context ctx, dreal_expr y, dreal_expr z, string name, unsigned num);
    dreal_expr dreal_mk_XOR(dreal_context ctx, dreal_expr y, dreal_expr z, string name, unsigned num);
    dreal_expr dreal_mk_SREM(dreal_context ctx, dreal_expr y, dreal_expr z, string name);
    dreal_expr dreal_mk_ASHR(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num);
    dreal_expr dreal_mk_SHL(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num);
    dreal_expr dreal_mk_INT_cmp(dreal_context ctx, dreal_expr y, dreal_expr z, Op_m pvop, string name);
    int getCMP(int rl, int rr, Op_m pvop);
    dreal_expr tran_constraint(Constraint *con, UnlinearVarTable *table, int time);
    void get_constraint(vector<Constraint> consList, UnlinearVarTable *table, int time, bool isTransition);
    void encode_path(CFG* ha, vector<int> patharray);

    std::vector<IndexPair> index_cache; 
    std::vector<IndexPair> core_index;

    bool analyze_unsat_core(int state);
    void add_IIS(IndexPair index);

    void clear(){
        index_cache.clear();
        core_index.clear();
        delete table;

        dreal_reset(ctx);
        //dreal_del_context(ctx);
        ctx = dreal_mk_context(qf_nra);
        dreal_set_precision(ctx, precision);
    }
public:
    UnlinearVerify(){
        dreal_init();
        ctx = dreal_mk_context(qf_nra);
        table=NULL;
        time=0;
    }
    UnlinearVerify(double pre, DebugInfo *d, int mode){
        dreal_init();
        ctx = dreal_mk_context(qf_nra);
        table=NULL;
        this->precision = pre;
        dreal_set_precision(ctx, pre);
        this->dbg = d;
        this->outMode = mode;
        time=0;
    }
    void setPrecision(double pre){
        this->precision = pre;
        dreal_set_precision(ctx, pre);
    }
    void setDebugInfo(DebugInfo *dbg){
        this->dbg = dbg;
    }
    void setOutMode(int output){
        this->outMode = output;
    }
    bool check(CFG* ha, vector<int> path);
    vector<IndexPair> get_core_index(){return core_index;}
    ~UnlinearVerify(){delete table; dreal_del_context(ctx);index_cache.clear();core_index.clear();}
    void print_sol(CFG* cfg);

    double getTime(){return time;}
};



#endif

