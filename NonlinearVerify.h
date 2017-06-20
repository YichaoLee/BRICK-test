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
    dreal::solver s;
    int var_num;
    int alloca_num;
    map<int, double> varVal;
    map<int, int>storeMap;
    map<int, int> alias;
    vector<dreal::expr> x;
    map<int, int> exprMap;
    CFG *cfg;
public:
    NonlinearVarTable(dreal::solver &c, CFG *ha);

    ~NonlinearVarTable();

    void setX(int ID, int time, VarType type);
    int alloca();
    void setAlias(int ID1, int ID2);
    void setAlias(Variable *v1, Variable *v2);
    void setVal(int ID, double val);
    void store(int ID1, int ID2);
    int getNum();
    dreal::expr getX(int ID);
    void setX(int ID, dreal::expr expression);
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
    dreal::solver s;
    NonlinearVarTable *table;
    double solverTime;
    double precision;
    int outMode;
    DebugInfo *dbg;

    dreal::expr getExpr(Variable *v, bool &treat, double &val, NonlinearVarTable *table);
    void dreal_mk_tobv_expr(dreal::expr x, string name, unsigned num, vector<dreal::expr> &xbv);
    dreal::expr dreal_mk_AND(dreal::expr y, dreal::expr z, string yname, string zname, unsigned num);
    dreal::expr dreal_mk_NAND(dreal::expr y, dreal::expr z, string yname, string zname, unsigned num);
    dreal::expr dreal_mk_OR(dreal::expr y, dreal::expr z, string yname, string zname, unsigned num);
    dreal::expr dreal_mk_XOR(dreal::expr y, dreal::expr z, string yname, string zname, unsigned num);
    dreal::expr dreal_mk_REM(dreal::expr y, dreal::expr z, string name);
    dreal::expr dreal_mk_ASHR(dreal::expr y, int rr, string name, unsigned num);
    dreal::expr dreal_mk_LSHR(dreal::expr y, int rr, string name, unsigned num);
    dreal::expr dreal_mk_SHL(dreal::expr y, int rr, string name, unsigned num);
    dreal::expr dreal_mk_INT_cmp(dreal::expr y, dreal::expr z, Op_m pvop, string name);
    int getCMP(int rl, int rr, Op_m pvop);

    dreal::expr mk_compare_ast(Constraint *con, NonlinearVarTable *table);
    dreal::expr mk_assignment_ast(Constraint *con, NonlinearVarTable *table, int time);
    dreal::expr mk_ptr_operation_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);
    dreal::expr mk_convert_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);
    dreal::expr mk_binaryop_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);
    dreal::expr mk_compare_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);
    dreal::expr mk_function_expr(Variable *lv, ParaVariable rpv, NonlinearVarTable *table, int time);

    dreal::expr tran_constraint(Constraint *con, NonlinearVarTable *table, int time);
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
        s.set_delta(pre);
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

