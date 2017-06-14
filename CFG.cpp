#include "CFG.h"
using namespace std;
int Transition::tran_id = 0;


void printPath(CFG *cfg, vector<int> path){
    cerr<<"Path route: ";
    for(unsigned i=0;i<path.size();i++){
        int id = path[i];
        State *s = cfg->searchState(id);
        if(s==NULL) cerr<<"printPath state error "<<id<<"\n";
        if(i<path.size()-1){
            cerr<<s->name<<"->";
            Transition *t = cfg->searchTransition(path[++i]);
            if(t==NULL) cerr<<"\nprintPath transition error "<<path[i]<<"\n";
            assert(t!=NULL);
            cerr<<t->name<<"->";
        }
        else
            cerr<<s->name<<"("<<s->ID<<")"<<endl;
    }
}

void CFG::InsertCFGState(int id,string name,string funcName)
{
    State* tmp = new State(id,name,funcName);
    this->stateMap.insert(pair<int,State*>(tmp->ID,tmp));
}

CFG  global_CFG;


 void CFG::InsertCFGTransition(Transition* tr)
 {
     this->transitionMap.insert(pair<int,Transition*>(tr->ID,tr));
 }

void CFG::InsertCFGLabel(string Label, State *s){
    LabelMap.insert( pair<string,State*> (Label,s));

        for(unsigned int i=0;i<transitionList.size();i++){

                if(transitionList[i].toLabel == Label&&transitionList[i].toState==NULL)
                {                   
                    transitionList[i].toName = s->name;
                    transitionList[i].toState = s;
                    //errs()<<"SLOT%"<<Label<<"\tsName:\t"<<s->name<<"\n\n\n";
                };
        }   
        for(unsigned int i=0;i<stateList.size();i++)
        {
            State s1= stateList[i];
            for(unsigned int j=0;j<s1.transList.size();j++)
            {
                if(s1.transList[j]->toLabel == Label && s1.transList[j]->toState == NULL)
                {
                    s1.transList[j]->toName = s->name;
                    s1.transList[j]->toState = s;
                }
            }
        }
        errs()<<"func\t"<<Label <<"\t"<< s->name<<"\n";
}

//stateList&transitionList----->Map
bool CFG::initial(){
    stateMap.clear();
    stateStrMap.clear();
    nameMap.clear();
    transitionMap.clear();
    transitionStrMap.clear();
    this->counter_transition = 0;    
/*
        for(int i=0;i<stateList.size();i++)
        errs()<<stateList[i]<<"\n";
    
        for(int i=0;i<transitionList.size();i++)
        errs()<<transitionList[i]<<"\n";
*/
    int count=1;
    for(unsigned int i=0;i<stateList.size();i++){    
        State* st=&stateList[i];
//        errs()<<st->ID<<"\t"<<st->nextS<<"\n";
        st->transList.clear();
        if(i==0){
//            initialState=st;
            st->ID=0;
//            st->isInitial=true;
        }
        else
            st->ID=count++;    
        if(st->isInitial)
            initialState=st;
        stateMap.insert(pair<int, State*>(st->ID, st));
        stateStrMap.insert(pair<string, State*>(st->name, st));
        nameMap.insert(pair<int, string>(st->ID, st->name));
        for(unsigned int j=0;j<transitionList.size();j++){
            Transition* tran=&transitionList[j];
            if(st->name==tran->fromName){
                st->transList.push_back(tran);
                tran->fromState=st;
            }
            else if(st->name==tran->toName){                
                tran->toState=st;
            }
        }
    }
    for(unsigned int i=0;i<transitionList.size();i++){
        Transition* tran=&transitionList[i];
        tran->ID=count++;        
        transitionMap.insert(pair<int, Transition*>(tran->ID,tran));
        transitionStrMap.insert(pair<string, Transition*>(tran->name, tran));
        nameMap.insert(pair<int, string>(tran->ID, tran->name));
        if(tran->toState==NULL){
            errs()<<"warning: can not find the tostate of the transition: "<<tran->name<<"\n";
            errs()<<tran->name<<" toLabel "<<tran->toLabel<<"\n";
//            return false;
        }
    }
    if(initialState==NULL){
        errs()<<"Warning: there is no initial state.\n";
        State* st=&stateList[0];
        st->isInitial=true;
        initialState=st;
//        return false;
    }
//    errs()<<"cfg initialed~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n";
    return true;    

}

bool CFG::isLinear(){
    return linear;
} 

void CFG::setModeLock(){
    modeLock = true;
}

void CFG::setUnlinear(){
    if(!modeLock)
       linear = false;
}

void CFG::setLinear(){
    if(!modeLock)
       linear = true;
}

bool CFG::is_state(const int ID){
    if((unsigned)ID < stateList.size())
      return true;
    return false;
}
bool CFG::hasVariable(string name){
    for(unsigned int i = 0; i < variableList.size(); i ++){
        if(variableList[i].name == name)
            return true;
    }
    return false;
}
Variable* CFG::getVariable(string name){
    Variable* var = NULL;
    for(unsigned int i = 0; i < variableList.size(); i ++){
        if(variableList[i].name == name)
            var = &(variableList[i]);
    }
    return var;
}
string CFG::getNodeName(int i){
    if(nameMap.find(i)==nameMap.end())
        return string();
    return nameMap[i];
}
State* CFG::searchState(int stateID) {
    if(stateMap.find(stateID)==stateMap.end())
        return NULL;
    return stateMap[stateID];
}

Transition* CFG::searchTransition(int transID) {        
    if(transitionMap.find(transID)==transitionMap.end())
        return NULL;
    return transitionMap[transID];
}


raw_ostream& operator << (raw_ostream& os,Op_m& object){
    switch(object){
        case TRUNC:errs()<<" trunc ";break;
        case ZEXT:errs()<<" zext ";break;
        case SEXT:errs()<<" sext ";break;
        case FPTRUNC:errs()<<" fptrunc ";break;
        case FPEXT:errs()<<" fpext ";break;
        case FPTOUI:errs()<<" fptoui ";break;
        case FPTOSI:errs()<<" fptosi ";break;
        case UITOFP:errs()<<" uitofp ";break;
        case SITOFP:errs()<<" sitofp ";break;
        case BITCAST:errs()<<" bitcast ";break;
        case ADD:case FADD:errs()<<" + ";break;
        case SUB:case FSUB:errs()<<" - ";break;
        case AND:errs()<<" and ";break;
        case NAND:errs()<<" nand ";break;
        case OR:errs()<<" or ";break;
        case XOR:errs()<<" xor ";break;
        case TAN:errs()<<" tan ";break;
        case ATAN:errs()<<" atan ";break;
        case ATAN2:errs()<<" atan2 ";break;
        case SIN:errs()<<" sin ";break;
        case ASIN:errs()<<" asin ";break;
        case COS:errs()<<" cos ";break;
        case ACOS:errs()<<" acos ";break;
        case SQRT:errs()<<" sqrt ";break;
        case POW:errs()<<" pow ";break;
        case LOG:errs()<<" log ";break;
        case LOG10:errs()<<" log10 ";break;
        case ABS:errs()<<" abs ";break;
        case FABS:errs()<<" fabs ";break;
        case EXP:errs()<<" exp ";break;
        case SINH:errs()<<" sinh ";break;
        case COSH:errs()<<" cosh ";break;
        case TANH:errs()<<" tanh ";break;
        case MUL:case FMUL:errs()<<" * ";break;
        case SDIV:case UDIV:case FDIV:errs()<<" / ";break;
        case GETPTR:errs()<<" getptr ";break;
        case ADDR:errs()<<" addr ";break;
        case STORE:errs()<<" store ";break;
        case LOAD:errs()<<" load ";break;
        case ALLOCA:errs()<<" alloca ";break;
        case SREM:case UREM:case FREM:errs()<<" % ";break;
        case ASHR:case LSHR:errs()<<" >> ";break;
        case SHL:errs()<<" << ";break;
        case slt:case ult:case flt:errs()<<" < ";break;
        case sle:case ule:case fle:errs()<<" <= ";break;
        case sgt:case ugt:case fgt:errs()<<" > ";break;
        case sge:case uge:case fge:errs()<<" >= ";break;
        case eq:case feq:errs()<<" == ";break;
        case ne:case fne:errs()<<" != ";break;
        case ISNAN:errs()<<" isnan ";break;
        case ISINF:errs()<<" isinf ";break;
        case ISNORMAL:errs()<<" isnormal ";break;
        case ISFINITE:errs()<<" isfinite ";break;
        case SIGNBIT:errs()<<" signbit ";break;
        case CLASSIFY:errs()<<" fpclassify ";break;
        case NONE:errs()<<" ";break;
    }
    return os;
}

raw_ostream& operator << (raw_ostream& os,Err& object){
    switch(object){
        case Assert:errs()<<" Assert Error ";break;
        case Spec:errs()<<" Spec Error ";break;
        case Div0:errs()<<" Div0 Error ";break;
        case DomainLog:errs()<<" DomainLog Error ";break;
        case DomainSqrt:errs()<<" DomainSqrt Error ";break;
        case DomainTri:errs()<<" DomainTri Error ";break;
        case Noerr:errs()<<" No Error ";break;
    }
    return os;
}


extern string get_m_Operator_str(Op_m op){
    switch(op){
        case TRUNC:return " trunc ";break;
        case ZEXT:return " zext ";break;
        case SEXT:return " sext ";break;
        case FPTRUNC:return " fptrunc ";break;
        case FPEXT:return " fpext ";break;
        case FPTOUI:return " fptoui ";break;
        case FPTOSI:return " fptosi ";break;
        case UITOFP:return " uitofp ";break;
        case SITOFP:return " sitofp ";break;
        case BITCAST:return " bitcast ";break;
        case GETPTR:return " getptr ";break;
        case ADD:case FADD:return " + ";break;
        case SUB:case FSUB:return " - ";break;
        case AND:return " and ";break;
        case NAND:return " nand ";break;
        case OR:return " or ";break;
        case XOR:return " xor ";break;
        case TAN:return " tan ";break;
        case ATAN:return " atan ";break;
        case ATAN2:return " atan2 ";break;
        case SIN:return " sin ";break;
        case ASIN:return " asin ";break;
        case COS:return " cos ";break;
        case ACOS:return " acos ";break;
        case SQRT:return " sqrt ";break;
        case POW:return " pow ";break;
        case LOG:return " log ";break;
        case LOG10:return " log10 ";break;
        case ABS:return " abs ";break;
        case FABS:return " fabs ";break;
        case EXP:return " exp ";break;
        case SINH:return " sinh ";break;
        case COSH:return " cosh ";break;
        case TANH:return " tanh ";break;
        case MUL:case FMUL:return " * ";break;
        case UDIV:case SDIV:case FDIV:return " / ";break;
        case ADDR:return " addr ";break;
        case STORE:return " store ";break;
        case LOAD:return " load ";break;
        case ALLOCA:return " alloca ";break;
        case SREM:case UREM:case FREM:return " % ";break;
        case ASHR:case LSHR:return " >> ";break;
        case SHL:return " << ";break;
        case NONE:return " ";break;
        case slt:case ult:case flt:return " < ";break;
        case sle:case ule:case fle:return " <= ";break;
        case sgt:case ugt:case fgt:return " > ";break;
        case sge:case uge:case fge:return " >= ";break;
        case eq:case feq:return " == ";break;
        case ne:case fne:return " != ";break;
        case ISNAN:return " isnan ";break;
        case ISINF:return " isinf ";break;
        case ISNORMAL:return " isnormal ";break;
        case ISFINITE:return " isfinite ";break;
        case SIGNBIT:return " signbit ";break;
        case CLASSIFY:return " fpclassify ";break;
        default: assert(false);break;
    }
}

extern string get_var_type(VarType type){
    switch(type){
        case INT: return " INT ";break;
        case FP: return " FP ";break;
        case PTR: return " PTR ";break;
        case BOOL: return " BOOl ";break;
        case INTNUM: return " INTNUM ";break;
        case FPNUM: return " FPNUM ";break;
        default: assert(false);break;
    }
}

/******************************dReal_nonlinear_constraint************************************/
void Variable::printName(){
    if(type == FPNUM){
        if(numbits == 32){
            int32_t temp = atoi(name.c_str());
            float *fp = (float *)&temp;
            errs()<<*fp;
        }
        else if(numbits == 64){
            int64_t temp = atoll(name.c_str());
            double *fp = (double *)&temp;
            errs()<<*fp;
        }
    }
    else
        errs()<<name;
}

double Variable::getVal(){
    assert(type==INTNUM||type==FPNUM);
    if(type == FPNUM){
        if(numbits == 32){
            int32_t temp = atoi(name.c_str());
            float *fp = (float *)&temp;
            return (double)*fp;
        }
        else if(numbits == 64){
            int64_t temp = atoll(name.c_str());
            double *fp = (double *)&temp;
            return *fp;
        }
    }
    
    return ConvertToDouble(name);
}

raw_ostream& operator << (raw_ostream& os, Variable& object){
    errs()<<"name:"<<object.name<<" id:"<<object.ID<<" type:"<<get_var_type(object.type)<<" bits:"<<object.numbits;
    return os;
}



raw_ostream&  operator << (raw_ostream& os,ParaVariable& object){
    if(object.lvar!=NULL){
        object.lvar->printName();
    }
    errs()<<object.op;
    if(object.rvar!=NULL){
        object.rvar->printName();
    }
    for(unsigned i=0;i<object.varList.size();i++)
            errs()<<object.varList[i]->name<<" ";
    return os;
}

raw_ostream& operator << (raw_ostream& os,Operator& object){
    switch(object){
        case SLT:case ULT:case FLT:errs()<<" < ";break;
        case SLE:case ULE:case FLE:errs()<<" <= ";break;
        case SGT:case UGT:case FGT:errs()<<" > ";break;
        case SGE:case UGE:case FGE:errs()<<" >= ";break;
        case EQ:case FEQ:errs()<<" == ";break;
        case NE:case FNE:errs()<<" != ";break;
        case ASSIGN:errs()<<" = ";break;
    }
    return os;
}

raw_ostream& operator << (raw_ostream& os,Constraint& object){
    errs()<<"constraint:";    
    errs()<<object.lpvList;
    errs()<<object.op;
    errs()<<object.rpvList;

    return os;

}


raw_ostream& operator << (raw_ostream& os, Transition object){
    errs()<<"Transition Name:"<<object.name<<" ID:"<<object.ID<<"\n";
    errs()<<"Level:"<<object.level<<"\n";
    errs()<<"ToLabel:"<<object.toLabel<<"\n";
    errs()<<"from:"<<object.fromName<<" to:"<<object.toName<<"\nGuard:\n";
    if(object.guardList.empty())
        errs()<<"null\n";
    else{
        for(unsigned int i=0;i<object.guardList.size();i++)
            errs()<<"\t"<<object.guardList[i]<<"\n";
        errs()<<"\n";
    }
    return os;
}

raw_ostream& operator << (raw_ostream& os, State object){
    errs()<<"Location Name:"<<object.funcName<<" "<<object.name<<" ID:"<<object.ID<<" nextS:"<<object.nextS<<"\n";
    errs()<<"Level:"<<object.level<<"\n";
    errs()<<"ErrorType:"<<object.error<<"\n";
    if(object.isInitial)
      errs()<<"\tInitial location\n";
    if(object.consList.empty())
        errs()<<"null\n";
    else{
        for(unsigned int i=0;i<object.consList.size();i++)
            errs()<<"\t"<<object.consList[i]<<"\n";
        errs()<<"\n";
    }
    errs()<<"Content:"<<object.ContentRec<<"\n";
    return os;
}

void CFG::print(){
    errs()<<"*******************CFG Information*********************\n";
    errs()<<"CFG:"<<name<<"\n";
    printLinearMode();
    unsigned mainInputID=0;
    unsigned mainSize = mainInput.size();
    for(unsigned i=0;i<exprList.size();i++){ 
	if(exprList[i].type==PTR)
		continue;
	errs()<<"(declare-fun ";
	errs()<<exprList[i].name;
	errs()<<" () ";
	if(exprList[i].type==INT)
		errs()<<"Int";
	else
		errs()<<"Real";
	errs()<<")\n";
    }
    for(unsigned i=0;i<variableList.size();i++){ 
        errs()<<variableList[i];
        // errs()<<"variable:"<<variableList[i].name;
        // errs()<< ", " << variableList[i].ID;
        // errs()<<", "<<get_var_type(variableList[i].type)<<variableList[i].numbits;
        if(mainInputID<mainSize){
            if(mainInput[mainInputID]==i){
                errs()<<", mainInput";
                mainInputID++;
            }
        }
        errs()<<"\n";
    }
    errs()<<"\n";
    for(unsigned int i=0;i<stateList.size();i++)
          errs()<<stateList[i]<<"\n";
    for(unsigned int i=0;i<transitionList.size();i++)
        errs()<<transitionList[i]<<"\n";
}   
   
void CFG::printLinearMode(){
	errs()<<"VerifierMode:\t";
    if(linear)
        errs()<<"Linear\n";
    else
        errs()<<"Unlinear\n";
}

Operator getEnumOperator(string str)
{

    if(str=="EQ")
        return EQ;
    else if(str=="NE")
        return NE;
    else if(str=="SLT")
        return SLT;
    else if(str=="SLE")
        return SLE;
    else if(str=="SGE")
        return SGE;
    else if(str=="SGT")
        return SGT;
    else if(str=="ULT")
        return ULT;
    else if(str=="ULE")
        return ULE;
    else if(str=="UGE")
        return UGE;
    else if(str=="UGT")
        return UGT;
    else if(str=="FEQ")
        return FEQ;
    else if(str=="FNE")
        return FNE;
    else if(str=="FLT")
        return FLT;
    else if(str=="FLE")
        return FLE;
    else if(str=="FGE")
        return FGE;
    else if(str=="FGT")
        return FGT;
    else if(str=="ASSIGN")
        return ASSIGN;
    else
        assert(false);
}

Op_m get_m_Operator(string str){

    if(str=="tan")
        return TAN;
    else if(str=="atan")
        return ATAN;
    else if(str=="atan2")
        return ATAN2;
    else if(str=="sin")
        return SIN;
    else if(str=="asin")
        return ASIN;
    else if(str=="cos")
        return COS;
    else if(str=="acos")
        return ACOS;
    else if(str=="sqrt")
        return SQRT;
    else if(str=="pow")
        return POW;
    else if(str=="log")
        return LOG;
    else if(str=="abs")
        return ABS;
    else if(str=="fabs")
        return FABS;
    else if(str=="exp")
        return EXP;
    else if(str=="sinh")
        return SINH;
    else if(str=="cosh")
        return COSH;
    else if(str=="tanh")
        return TANH;
    else if(str=="mul")
        return MUL;
    else if(str=="fmul")
        return FMUL;
    else if(str=="sdiv")
        return SDIV;
    else if(str=="fdiv")
        return FDIV;
    else if(str=="udiv")
        return UDIV;
    else if(str=="add")
        return ADD;
    else if(str=="fadd")
        return FADD;
    else if(str=="sub")
        return SUB;
    else if(str=="fsub")
        return FSUB;
    else if(str=="and")
        return AND;
    else if(str=="nand")
        return NAND;
    else if(str=="or")
        return OR;
    else if(str=="xor")
        return XOR;
    else if(str=="log10")
        return LOG10;
    else if(str=="srem")
        return SREM;
    else if(str=="urem")
        return UREM;
    else if(str=="frem")
        return FREM;
    else if(str=="ashr")
        return ASHR;
    else if(str=="lshr")
        return LSHR;
    else if(str=="shl")
        return SHL;
    else if(str=="trunc")
        return TRUNC;
    else if(str=="zext")
        return ZEXT;
    else if(str=="sext")
        return SEXT;
    else if(str=="fptrunc")
        return FPTRUNC;
    else if(str=="fpext")
        return FPEXT;
    else if(str=="fptoui")
        return FPTOUI;
    else if(str=="fptosi")
        return FPTOSI;
    else if(str=="uitofp")
        return UITOFP;
    else if(str=="sitofp")
        return SITOFP;
    else if(str=="bitcast")
        return BITCAST;
    else if(str=="EQ")
        return eq;
    else if(str=="NE")
        return ne;
    else if(str=="SLT")
        return slt;
    else if(str=="SLE")
        return sle;
    else if(str=="SGE")
        return sge;
    else if(str=="SGT")
        return sgt;
    else if(str=="ULT")
        return ult;
    else if(str=="ULE")
        return ule;
    else if(str=="UGE")
        return uge;
    else if(str=="UGT")
        return ugt;
    else if(str=="FEQ")
        return feq;
    else if(str=="FNE")
        return fne;
    else if(str=="FLT")
        return flt;
    else if(str=="FLE")
        return fle;
    else if(str=="FGE")
        return fge;
    else if(str=="FGT")
        return fgt;
    else if(str.find("isnan") != string::npos)
        return ISNAN;
    else if(str.find("isinf") != string::npos)
        return ISINF;
    else if(str.find("isnormal") != string::npos)
        return ISNORMAL;
    else if(str.find("finite") != string::npos)
        return ISFINITE;
    else if(str.find("signbit") != string::npos)
        return SIGNBIT;
    else if(str.find("fpclassify") != string::npos)
        return CLASSIFY;
    else
        return NONE;
}


string intToString(int value)  
{  
    char tmpString[15];  
    memset(tmpString, 0x00, 15);  
    sprintf(tmpString, "%d", value);  
    return  tmpString;  
}

