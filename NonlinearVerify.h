#ifndef _Nonlinearverify_h
#define _Nonlinearverify_h
#include "CFG.h"
#include "general.h"
#include <stdio.h>
#include <cstdlib>
#include <sstream>
#include <cstring>
#include "dreal/dreal.hh"
#include "dreal/dreal.h"
//#include "Solver.h"
//#include "dreal_c.h"
#include <fstream>
#include "math.h"
#include "DebugInfo.h"

extern int smt2set_in   (FILE *);
extern int smt2parse    ();
extern int m_argc;
extern char ** m_argv;

class NonlinearVarTable{
private:
    dreal_context ctx;
    int var_num;
    int alloca_num;
    map<int, double> varVal;
    map<int, int>storeMap;
    map<int, int> alias;
    vector<dreal_expr> x;
    map<int, int> exprMap;
    CFG *cfg;
public:
    NonlinearVarTable(dreal_context &c, CFG *ha);

    ~NonlinearVarTable();

    void setX(int ID, int time, VarType type);
    int alloca();
    void setAlias(int ID1, int ID2);
    void setAlias(Variable *v1, Variable *v2);
    void setVal(int ID, double val);
    void store(int ID1, int ID2);
    int getNum();
    dreal_expr getX(int ID);
    void setX(int ID, dreal_expr expr);
    int load(int ID);
    bool hasAlias(Variable *v);
    Variable* getAlias(int ID);

    Variable* getAlias(Variable* var);
    bool getVal(Variable *var, double &v);
    bool getVal(int ID, double &v);
    void printAliasMap();
    map<int, double> getValmap();
    map<int, int> getAliasmap();
    CFG *getCFG();
};

class NonlinearVerify: public Verify{

    string smt;
    dreal_context ctx;
    dreal::solver s;
    NonlinearVarTable *table;
    double solverTime;
    double precision;
    int outMode;
    DebugInfo *dbg;

    dreal_expr getExpr(Variable *v, bool &treat, double &val, NonlinearVarTable *table);
    void dreal_mk_tobv_expr(dreal_context ctx, dreal_expr x, string name, unsigned num, vector<dreal_expr> &xbv);
    dreal_expr dreal_mk_AND(dreal_context ctx, dreal_expr y, dreal_expr z, string yname, string zname, unsigned num);
    dreal_expr dreal_mk_NAND(dreal_context ctx, dreal_expr y, dreal_expr z, string yname, string zname, unsigned num);
    dreal_expr dreal_mk_OR(dreal_context ctx, dreal_expr y, dreal_expr z, string yname, string zname, unsigned num);
    dreal_expr dreal_mk_XOR(dreal_context ctx, dreal_expr y, dreal_expr z, string yname, string zname, unsigned num);
    dreal_expr dreal_mk_REM(dreal_context ctx, dreal_expr y, dreal_expr z, string name);
    dreal_expr dreal_mk_ASHR(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num);
    dreal_expr dreal_mk_LSHR(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num);
    dreal_expr dreal_mk_SHL(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num);
    dreal_expr dreal_mk_INT_cmp(dreal_context ctx, dreal_expr y, dreal_expr z, Op_m pvop, string name);
    int getCMP(int rl, int rr, Op_m pvop);

    dreal_expr mk_compare_ast(Constraint *con, NonlinearVarTable *table);
    dreal_expr mk_assignment_ast(Constraint *con, NonlinearVarTable *table, int time);
    dreal_expr mk_ptr_operation_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);
    dreal_expr mk_convert_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);
    dreal_expr mk_binaryop_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);
    dreal_expr mk_compare_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);
    dreal_expr mk_function_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);

    dreal_expr tran_constraint(Constraint *con, NonlinearVarTable *table, int time);
    void get_constraint(vector<Constraint> &consList, NonlinearVarTable *table, int time, bool isTransition);
    void encode_path(CFG* ha, vector<int> &patharray);

    std::vector<IndexPair> index_cache; 
    std::vector<IndexPair> core_index;

    bool analyze_unsat_core(int state);
    void add_IIS(IndexPair index);

    void clear();
    void reset();
public:
    NonlinearVerify();
    NonlinearVerify(double pre, DebugInfo *d, int mode);
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
    bool check(CFG* ha, vector<int> &path);
    vector<IndexPair> get_core_index(){return core_index;}
    ~NonlinearVerify();
    void print_sol(CFG* cfg);

    double getTime(){return solverTime;}
};



#endif

