//Define the CFG's Data Structure
#ifndef  _CFG_H___
#define  _CFG_H___
#include <iostream>
#include <string>
#include <vector> 
#include <list>
#include <fstream>
#include <map>
#include <stdlib.h> 
#include <assert.h>
#include "llvm/IR/BasicBlock.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h" 
#include <vector> 
#include "convinent.h"
#include "assert.h"
#include "general.h"


using namespace std;
using namespace llvm;

enum Operator{
    ASSIGN,
    ASSUME,
    EQ,NE,
    SLT,SLE,SGT,SGE,
    ULT,ULE,UGT,UGE,
    FEQ,FNE,
    FLT,FLE,FGT,FGE,
};

enum Op_m{
    //convert
    TRUNC,ZEXT,SEXT,FPTRUNC,FPEXT,FPTOUI,FPTOSI,UITOFP,SITOFP,
    //binary operation
    FADD,ADD,SUB,FSUB,MUL,FMUL,UDIV,SDIV,FDIV,
    UREM,SREM,FREM,
    LSHR,ASHR,SHL,AND,NAND,OR,XOR,
    //float lib
    MKNAN,ISNAN,ISINF,ISNORMAL,ISFINITE,SIGNBIT,CLASSIFY,
    FESETROUND,FEGETROUND,COPYSIGN,
    //math lib
    SINH,COSH,TANH,TAN,ATAN,ATAN2,SIN,ASIN,COS,ACOS,SQRT,POW,LOG,LOG10,EXP,
    ABS,FABS,
    CEIL,FLOOR,ROUND,FUNCTRUNC,NEARBYINT,RINT,
    FMAX,FMIN,FMOD,FDIM,REMAINDER,MODF,
    //ptr operation
    ADDR,GETPTR,STORE,LOAD,ALLOCA,BITCAST,
    //compare operation
    eq,ne,
    slt,sle,sgt,sge,
    ult,ule,ugt,uge,
    feq,fne,
    flt,fle,fgt,fge,
    NONE,
};

enum Err{
    Noerr,
    Assert,
    Spec,
    Div0,
    DomainLog,
    DomainSqrt,
    DomainTri
};

extern Operator getEnumOperator(string str);
extern Op_m get_m_Operator(string str,bool isFunc=false);
extern string get_m_Operator_str(Op_m op);
extern raw_ostream& operator << (raw_ostream& os,Operator& object);
extern raw_ostream& operator << (raw_ostream& os,Op_m& object);
extern raw_ostream& operator << (raw_ostream& os,Err& object);
string intToString(int value);

/*************************dReal_nonlinear*************************/
enum VarType{
    INTNUM,    //The var is a INT num
    FPNUM,    //The var is a FP num
    INT,    //The var store a INT type data
    FP,     //The var store a FP type data
    // FP32,     //The var store a 32bit-FP type data
    // FP64,     //The var store a 64bit-FP type data
    PTR,    //The var store a ID of a PTR var
    BOOL    //The var store a bool type data
};

class Variable{
    public:
        VarType type;
        string name;
        int ID;
        unsigned numbits;
        Variable(){type=FP;ID=-1;numbits=0;}
        Variable(string name1,int id,VarType ty,unsigned nb){name=name1;ID=id;type=ty;numbits=nb;}
        Variable(const Variable &a){
            this->name=a.name;
            this->ID=a.ID;
            this->type=a.type;
            this->numbits=a.numbits;
        }
        Variable(const Variable *a){
            this->name=a->name;
            this->ID=a->ID;
            this->type=a->type;
            this->numbits=a->numbits;
        }
        void print(){errs()<<"name="<<name<<";id="<<ID;}
        void printName();
        double getVal();
        Variable& operator =(const Variable &a){
            this->name=a.name;
            this->ID=a.ID;
            this->type=a.type;
            this->numbits=a.numbits;
            return *this;
        }
        friend raw_ostream& operator << (raw_ostream& os, Variable& object);
};

class ParaVariable{
    public:
    bool isExp;
    Op_m op;
    Variable* lvar;
    Variable* rvar;
    vector<Variable*> varList;
        ParaVariable(){isExp=false;lvar=NULL;rvar=NULL,op=NONE;}
        ParaVariable(bool iE,Variable *lv,Variable *rv,string pm,Op_m opr ){isExp=iE;lvar=lv;rvar=rv;op=opr;}
    ParaVariable(const ParaVariable &a){
        this->isExp=a.isExp;
            this->lvar=a.lvar;
            this->rvar=a.rvar;
        this->op=a.op;
        this->varList=a.varList;
    }
    ~ParaVariable(){isExp=false;lvar=NULL;rvar=NULL;op=NONE;varList.clear();}
        ParaVariable& operator =(const ParaVariable &a){
        this->isExp=a.isExp;
            this->lvar=a.lvar;
            this->rvar=a.rvar;
        this->op=a.op;
        this->varList=a.varList;
            return *this;
        }
        void print(){
        if(lvar!=NULL)
                lvar->print();
            errs()<<op;
        rvar->print();
        for(unsigned i=0;i<varList.size();i++)
            errs()<<varList[i]<<", ";
        errs()<<"\n";
        }
        friend raw_ostream& operator << (raw_ostream& os,ParaVariable& object);
};


class Constraint{
    public:
        ParaVariable lpvList;
        ParaVariable rpvList;
        Operator op;
        Constraint(){};
        ~Constraint(){};
        Constraint& operator =(const Constraint &a){
            this->lpvList=a.lpvList;
            this->rpvList=a.rpvList;
            this->op=a.op;
            return *this;
        }
        friend raw_ostream& operator<<(raw_ostream& os, Constraint& object);
};


class Transition;
class State{
    public:
        bool isInitial;
        int ID;
        string funcName;
        int nextS;
        string name;
        int level;
        Err error;
        vector<Transition *> transList;     //zhuanyi List
        vector<Constraint> consList;        //fuzhi   List
        string ContentRec;                  //
        vector<int> locList;                //line number of the code
        State(){
            this->level = -1;
            this->ID = 0;
            this->name = "";
            this->funcName = "";
            this->isInitial = false;
            nextS = -1;
            error = Noerr;
        }
        State(int id,string name,string funcName)
        {
            this->level = -1;
            this->ID = id;
            this->name = name;
            this->funcName = funcName;
            this->isInitial = false;
            nextS = -1;
            error = Noerr;
        }
        State(bool bo,int id,string name1,string funcName1){
            isInitial = bo;
            ID = id;
            name = name1;
            funcName = funcName1;
            nextS = -1;
            level = -1;
            error = Noerr;
        }
        void InsertTransition(Transition* tr){ this->transList.push_back(tr);};
        void InsertConstraint(Constraint tr){ this->consList.push_back(tr);};
        State& operator =(const State &a){
            this->isInitial=a.isInitial;
            this->ID=a.ID;
            this->name=a.name;
            this->funcName = a.funcName;
            this->nextS=a.nextS;
            this->transList=a.transList;
            this->ContentRec=a.ContentRec;
            this->consList=a.consList;
            this->locList=a.locList;
            this->level=a.level;
            this->error=a.error;
            return *this;
        }
        friend raw_ostream& operator << (raw_ostream& os, State object);
};

class Transition{
    public:
        int ID;
        static int tran_id;
        string name;
        State* fromState;
        State* toState;
        string fromName;
        string toName;
        string toLabel;
        int level;
        vector<Constraint> guardList;
        Transition(int id,string name1):ID(id),name(name1){toLabel="";level =-1;};
        Transition(string fromName,string toName)
        {
            this->fromName = fromName;
            this->toName = toName;
            this->ID = tran_id++;
            this->level = -1;
        }
        Transition& operator =(const Transition a){
            this->ID=a.ID;
            this->tran_id=a.tran_id;
            this->name=a.name;
            this->fromName=a.fromName;
            this->toName=a.toName;
            this->fromState=a.fromState;
            this->toState=a.toState;
            this->toLabel=a.toLabel;
            this->guardList=a.guardList;
            this->level=a.level;
            return *this;
        }
        friend raw_ostream& operator << (raw_ostream& os, Transition object);
};    

class CFG{
    private:
        map<int,State*> stateMap;
        map<int,Transition*> transitionMap;
        map<string,State*> stateStrMap;
        map<string,Transition*> transitionStrMap;
        map<int,string> nameMap;
        bool linear;
        bool modeLock;
    public:
        map<string,State*> LabelMap;
        map<string,vector<string>> CallLabel;
        map<string, int> funcTime;
        map<string, string> endBlock;
        vector<string> retVar;
        list<ParaVariable> callVar;
        list<Constraint> initialCons;
        
        string name;
        string startFunc;
        unsigned counter_state;
        unsigned counter_s_state;
        unsigned counter_q_state;
        unsigned counter_variable;
        unsigned counter_transition;
        State* initialState;
        vector<State> stateList;
        vector<Transition> transitionList;//at the same time  ,equals to the transList
        vector<Variable> variableList;
        vector<Variable> exprList;
        vector<unsigned> mainInput;
        //vector<Transition*> transitionList1;
        Constraint c_tmp1;
        Constraint c_tmp2;
        //int transitionNum;
        CFG(){     
            counter_state = 0;
            counter_variable = 0;
            counter_s_state = 0;
            counter_q_state = 0;
            counter_transition = 0;
            linear=true;
            modeLock=false;
        }
        void print();
        void printLinearMode();
        bool initial();
        bool is_state(const int ID);
        bool isLinear();
        void setModeLock();
        void setLinear();
        void setUnlinear();
        bool hasVariable(string name);
        Variable* getVariable(string name);
        void InsertCFGState(int id,string name,string funcName);
        void InsertCFGTransition(Transition* tr);
        void InsertCFGLabel(string Label, State *s);
        void CFGStateConsList(int id,int op1);
        State* getState(int id){ return stateMap.find(id)->second;};
        State* getLabelState(string Label){
            map<string ,State* >::iterator l_it;
            l_it=LabelMap.find(Label);
            if(l_it==LabelMap.end())
                return NULL;
            else
                return l_it->second;};
        string getNodeName(int i);
        State* searchState(int stateID);
        State* searchState(string name);
        Transition* searchTransition(string name);
        Transition* searchTransition(int transID);
        Transition* searchTransitionByState(int from,int to);
        CFG& operator =(const CFG a){
            this->name=a.name;
            this->initialState=a.initialState;
            this->stateList=a.stateList;
            this->transitionList=a.transitionList;
            this->variableList=a.variableList;
            this->counter_state = a.counter_state;
            this->counter_variable = a.counter_variable;
            this->counter_s_state = a.counter_s_state;
            this->counter_q_state = a.counter_q_state;
            this->counter_transition = a.counter_transition;
            return *this;
        };

};
extern CFG global_CFG;

class IndexPair{
public:
    int start;
    int end;
    IndexPair(int _start,int _end):start(_start),end(_end){}
    bool contain(IndexPair& index){return start>=index.start && end<=index.end;}
    void print(){errs()<<"("<<start<<","<<end<<")";}
};

class Verify{
public:
    Verify(){};
    virtual ~Verify();
    virtual bool check(CFG* ha, vector<int> &path)=0;
    virtual vector<IndexPair> get_core_index()=0;
    // virtual void print_sol(CFG* cfg)=0;
    virtual double getTime()=0;
};

void printPath(CFG *cfg, vector<int> path);


#endif

