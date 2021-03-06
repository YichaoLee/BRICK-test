#ifndef _unlineaz3rverify_h
#define _unlineaz3rverify_h
#include "CFG.h"
#include "general.h"
#include <stdio.h>
#include <cstdlib>
#include <sstream>
#include <cstring>
#include "z3++.h"
#include "MUSSAnalyzer.h"
#include "math.h"
#include "DebugInfo.h"


class NonlinearZ3VarTable{
private:
    int var_num;
    int alloca_num;
    map<int, double> varVal;
    map<int, int>storeMap;
    map<int, int> alias;
    vector<z3::expr> x;
    map<int, int> exprMap;
    CFG *cfg;

public:
    NonlinearZ3VarTable(z3::context &ctx, CFG *ha);
    ~NonlinearZ3VarTable();
    void setX(int ID, int time, VarType type, unsigned numBits, z3::context &ctx);
    int alloca();
    void setAlias(int ID1, int ID2);
    void setAlias(Variable *v1, Variable *v2);
    void setVal(int ID, double val);
    void store(int ID1, int ID2);
    int getNum();
    z3::expr getX(int ID);
    void setX(int ID, z3::expr expr);
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

class NonlinearZ3Verify: public Verify{
    z3::context c;
    int outMode;
    DebugInfo *dbg;
    double solverTime;
    
    void printVector(vector<int> &path);
    z3::expr_vector encode_path(CFG* ha, vector<int> &path);
    z3::expr getExpr(Variable *v, bool &treat, double &val, NonlinearZ3VarTable *table);
    z3::expr getCMPExpr(Variable *v, NonlinearZ3VarTable *table);
    // z3::expr mk_INT_cmp(z3::expr y, z3::expr z, Op_m pvop);
    char const* getRealVal(string str);
    int getCMP(double rl, double rr, Op_m pvop);
    z3::expr bvcal(z3::expr a, z3::expr b, Op_m op);
    ////////////////////////////////////////////
    z3::expr mk_eq_ast(z3::expr a, z3::expr b);
    z3::expr mk_compare_ast(Constraint *con, NonlinearZ3VarTable *table);
    z3::expr mk_assignment_ast(Constraint *con, NonlinearZ3VarTable *table, int time);
    z3::expr mk_ptr_operation_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time);
    z3::expr mk_convert_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time);
    z3::expr mk_binaryop_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time);
    z3::expr mk_compare_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time);
    z3::expr mk_function_expr(Variable *lv, ParaVariable rpv, NonlinearZ3VarTable *table, int time);
    ///////////////////////////////////////////
    bool get_constraint(Constraint *con, NonlinearZ3VarTable *table, int time, z3::expr_vector &p);
    bool analyze_unsat_core(SubsetSolver& csolver, MapSolver& msolver);
    bool analyze_nonlinear(z3::expr_vector problem);
    void add_IIS(IndexPair index);
    std::vector<IndexPair> index_cache; 
    std::vector<IndexPair> core_index;     
    void clear(){index_cache.clear();core_index.clear();}
public:
    NonlinearZ3Verify();
    NonlinearZ3Verify(DebugInfo *d, int mode);
    ~NonlinearZ3Verify();
    bool check(CFG* ha, vector<int> &path);
    vector<IndexPair> get_core_index(){return core_index;}
    double getTime(){return solverTime;}
    void print_sol(CFG* cfg);
};

#endif

