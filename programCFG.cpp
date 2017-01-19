#include "programCFG.h"
// #include "printSTL.h"
#include "llvm/Support/FileSystem.h"
#include "CFGWriter.h"
#include <stack>  
#include "llvm/Support/CommandLine.h"
#include <time.h>
using namespace std;
using namespace llvm;
//std::map<BasicBlock*, CFGNode>* ProgramCFG::nodes = NULL;
int CFGNode::counter_state = 0;
int CFGNode::counter_variable = 0;


//Command line argument
cl::opt<int>
lineNo("line",
        cl::desc("Line Number"), cl::value_desc("line"));
cl::opt<string>
funcname("func",
        cl::desc("Function Name"), cl::value_desc("function name"));
cl::opt<string>
filename("name",
        cl::desc("File Name"), cl::value_desc("name"));
cl::opt<int>
bound("bound",
        cl::desc("check bound"), cl::value_desc("check bound"));
cl::opt<double>
prec("pre",
        cl::desc("Precision"), cl::value_desc("precision"));
cl::opt<int>
modeNo("mode",
        cl::desc("Checkmode"), cl::value_desc("check mode"));
cl::opt<int>
outMode("output",
        cl::desc("Outputmode"), cl::value_desc("output mode"));
cl::opt<string>
check("expression",
        cl::desc("check"), cl::value_desc("check"));


bool if_a(char x){
    if((x<='z' && x>='a')||(x<='Z' && x>='A'))
        return true;
    else 
        return false;
}

bool if_num(char x){
    if(x<='9' && x>='0')
        return true;
    else 
        return false;
}

bool if_op(char x){
    if(x=='=' || x=='<' || x=='>'|| x=='!')
        return true;
    else 
        return false;
}

bool if_as(char x){
    if(x=='+' || x=='-'|| x=='*'|| x=='/')
        return true;
    else
        return false;
}

string& trim(string &str, string::size_type pos = 0)
{
    static const string delim = " \t"; //删除空格或者tab字符
    pos = str.find_first_of(delim, pos);
    if (pos == string::npos)
        return str;
    return trim(str.erase(pos, 1));
}


ParaVariable StringToPara(string checkstr, string funcName){
    ParaVariable ptemp;
    return ptemp;
}

void ProgramCFG::assertSpec(CFG *cfg, int line){
    for(unsigned int i=0;i<cfg->stateList.size();i++){
        if(cfg->stateList[i].error!=Noerr) continue;
        for(vector<int>::iterator it=cfg->stateList[i].locList.begin();it<cfg->stateList[i].locList.end();it++){
            if(*it==lineNo){
                target.push_back(cfg->stateList[i].ID);
                cfg->stateList[i].error=Spec;
                break;
            }
        }
    }
}

ProgramCFG::ProgramCFG(Module &m):M(m){

    root = NULL;
    nodes = NULL;

    clock_t start,finish;

    start=clock();
    errs() <<"START CHECK FUNCTION <"<<funcname<<"> in precision "<<prec<<"\n";
    this->precision = prec;
    this->mode = modeNo;
    this->output = outMode;
    printMode();

    //Create the cfg Structure
    CFG* cfg = new CFG();
    // cfg->setUnlinear();
    buildProgramCFG(m, cfg);
    cfg->initial();
    if(outMode==1)
        cfg->print();

    finish=clock();
    double buildTime = 1000*(double)(finish-start)/CLOCKS_PER_SEC;
    errs() << "#BUILDCFG Time: \t" << ConvertToString(buildTime) << "ms\n";

    if(outMode==1)
        dbg->print();
    
    if(dbg->loc>200){
        errs()<<"Loc larger than 200!\n";
        exit(-1);
    }
    int inputbound=bound;


    start=clock();


    BoundedVerification verify(cfg,inputbound,target,prec,dbg,output);
    verify.check(check);

    double solver_time = verify.getSolverTime();
    /*
    if(check=="")
    {
        BoundedVerification verify(cfg,inputbound,target,prec,dbg,output);   
        verify.check(dreal_time,check);
    }
    else {
        BoundedVerification verify(cfg,inputbound,target,prec,dbg,output);
        verify.check(dreal_time,check);
    
    }*/

    // BoundedVerification verify(cfg,inputbound,target,prec,dbg,output);
    // verify.check(dreal_time,check);


    errs() << "bound:\t" << bound <<"\tprecision:\t" << prec <<"\tfunctionName:\t" << funcname << "\tcheck:\t" << check << "\n";
//    errs() << "Time: \t" << ConvertToString(1000*(double)(finish-start)/CLOCKS_PER_SEC) << "ms \n";
    errs() << "#Solver Time: \t" << ConvertToString(solver_time/1000) << "s\n";
    double mem_used_peak = memUsedPeak();
    double cpu_time = cpuTime();
    char mem_str[64];
    if (mem_used_peak != 0) 
        sprintf(mem_str, "#Memory used: %.2f MB\n", mem_used_peak);
    char time_str[64];
    sprintf(time_str, "#CPU Time: %g s\n", cpu_time);
    errs()<<time_str<<mem_str;
}

enum color{WHITE,BLACK,GRAY};
std::map<BasicBlock*, color> *colors;

std::map<Function*, std::vector<BasicBlock*> > *retBlocks;
std::set<Function*> *targetFunctionList; //only use in search

void ProgramCFG::printMode(){
    errs()<<"CheckMode: "<<mode<<"\t";
    switch(mode){
        case 0:errs()<<"Check assertions, div-0 and domain error\n";break;
        case 1:errs()<<"Check assertions only\n";break;
        case 2:errs()<<"Check div-0 and domain error only\n";break;
        default:errs()<<"Mode error\n";
    }
    errs()<<"OutMode: "<<outMode<<"\t";
    switch(outMode){
        case 0:errs()<<"Print Check result only\n";break;
        case 1:errs()<<"Print Check result with CFG and Constraints\n";break;
        default:errs()<<"OutMode error\n";
    }
}

void ProgramCFG::findAllRetBlocks(Module &m){
    for(Module::iterator f = m.begin(); f!= m.end(); f++){
        if(f->getName() == "main") continue;
        for(Function::iterator bb = f->begin(); bb != f->end(); bb++){
            TerminatorInst *terminator = bb->getTerminator();
            if(isa<ReturnInst>(terminator) ){
                ((*retBlocks)[f]).push_back(bb);
            }
        }
    }
}

void  ProgramCFG::setFuncVariable(const Function *F,string func, CFG* cfg, bool initial){
    for (Function::const_arg_iterator it = F->arg_begin(), E = F->arg_end();it != E; ++it) {
        Type *Ty = it->getType();
        unsigned numBits = getNumBits(it);

        if(initial){
            string varNum = it->getName();
            string varName = func+"_"+varNum;
            
            if(Ty->isPointerTy()){
                Type *ETy = Ty->getPointerElementType();
                int ID = cfg->counter_variable++;
                Variable var(varName, ID, PTR, 0);
                cfg->variableList.push_back(var);
                
                InstParser::setVariable(cfg, NULL, ETy, varName, true);
                
            }
            else{
                VarType type;
                if(Ty->isIntegerTy())
                    type = INT;
                else if(Ty->isFloatingPointTy())
                    type = FP;
                else
                    errs()<<"0:programCFG.type error\n";
                int ID = cfg->counter_variable++;
                Variable var(varName, ID, type, numBits);
                cfg->variableList.push_back(var);
                cfg->mainInput.push_back(ID);
            }
        }
        else{
            int ID = cfg->counter_variable++;
            string varNum = it->getName();
            string varName = func+"_"+varNum;
            
            VarType type;
            if(Ty->isPointerTy()){
                type = PTR;
                numBits = 0;
            }
            else if(Ty->isIntegerTy())
                type = INT;
            else if(Ty->isFloatingPointTy())
                type = FP;
            else
                errs()<<"1:programCFG.type error\n";

            if(!cfg->hasVariable(varName)){
                Variable var(varName, ID, type, numBits);
                cfg->variableList.push_back(var);
            }
            else
                errs()<<"1:setFuncVariable error 10086!!\t"<<varName<<"\n";
        }
    }
}

//build program cfg in the main source file !
void  ProgramCFG::buildProgramCFG(Module &m, CFG* cfg){
        if(funcname == "main"){
            cfg->startFunc = "main";
            dbg = new DebugInfo("main");
            readFunc("main", cfg, 0);
        }
        else{
            errs() <<  "Warning: There is no main function in the Module!\n";
            const Function *F = m.getFunction(funcname);
            if(!F)
                errs() <<  "Error: Can't find function "<<funcname<<" in the Module!\n";
            setFuncVariable(F, funcname, cfg, true);
            cfg->startFunc = funcname;
            dbg = new DebugInfo(funcname);

            map<string ,int >::iterator it=cfg->funcTime.find(funcname);
            if(it==cfg->funcTime.end())
                cfg->funcTime.insert(pair<string,int>(funcname,0));
            else
                errs()<<"ProgramCFG::buildProgramCFG error "<<funcname<<"\n";

            readFunc(funcname, cfg, 0);
        }    
}

void ProgramCFG::readFunc(string funcName, CFG *cfg, int time){
    Function *F = M.getFunction(funcName);  
    if(F == NULL){
        errs() <<  "error readFunc 10086!\t"<<funcName<<"\n";
        exit(-1) ;
    }

    if(time==0)
        dbg->getFuncInfo(F);

    for(Function::iterator bb = F->begin(); bb != F->end(); bb++){
        readBasicblock(bb, cfg, time);
    }
}

void ProgramCFG::readBasicblock(BasicBlock *b, CFG *cfg, int time){
    string callFunc;

    if(b){

        const Function* F = b->getParent()?b->getParent():nullptr;

/***********************ignore BB without predecessor ************************/
        
//       errs()<<"0:readBasicblock "<<F->getName()<<"\n";
        if (b!=&F->getEntryBlock()) {
            pred_iterator PI = pred_begin(b), PE = pred_end(b);
            if(PI == PE)
            return;
        }

        string func = F->getName();
        if(time>0)
        func = func+ConvertToString(time);
            //Generate a new state
        unsigned id = cfg->counter_state++;
        string  str = ConvertToString(cfg->counter_s_state);
        cfg->counter_s_state++;
        string name = "s"+str;
        State* s = new State(false, id, name, func);
        while(!cfg->initialCons.empty()){
            Constraint cTemp = cfg->initialCons.front();
            cfg->initialCons.pop_front();
            s->consList.push_back(cTemp);
        }
        cfg->stateList.resize(id+1);
        raw_ostream &ROS = errs();
        formatted_raw_ostream OS(ROS);

        global_CFG.InsertCFGState(cfg->counter_state,name,func);
            
//        errs()<<"0:readBasicblock "<<func<<"\n";
        if(func==cfg->startFunc && b==F->begin()){
            s->level=0;
            cfg->initialState=s;
            s->isInitial=true;
        }
        else if(b==F->begin()){
            setFuncVariable(F, func, cfg);
        }

            //Generate the new vector<Constraint>
        BasicBlock::iterator it_end = b->end();
        for(BasicBlock::iterator it = b->begin(); it != it_end; it ++){  

            const Instruction* I = dyn_cast<Instruction>(it);
            SlotTracker SlotTable(F);
            const Module* M = F?F->getParent():nullptr;
            InstParser W(OS, SlotTable, M, nullptr);
            W.setPrecision(precision);
            W.setMode(mode);

            // errs()<<"0.InL:";W.printInstructionLine(*I);
                //create the LabelMap
            if(it == b->begin()){
                bool hasFromS = W.InsertCFGLabel(cfg,b,s, func, "", false);
                if(!hasFromS){
                    cfg->counter_state--;
                    cfg->counter_s_state--;
                    return;
                }
                else if(s->level>bound){
                    if(cfg->stateList.size()<id)
                        cfg->stateList.resize(id);
                    cfg->stateList[s->ID]=(*s);
                    return;
                }
            } 

//            errs()<<"1:readBasicblock "<<func<<"\t"<<s->level<<"\t"<<s->ID<<"\n";
            //pre process before set constraints
            W.preprocess(cfg, s, I, func, target);
            // create the constraint table(NOT TRANSITION)
            W.setConstraint(cfg, s, it, func, bound, dbg);
                
            string op = I->getOpcodeName();
            // errs()<<"1:readBasicblock "<<func<<":"<<*I<<"\n";
            if(op=="call"){
                const CallInst *call = dyn_cast<CallInst>(I);
                Function *f = call->getCalledFunction();
                if(!f) 
                    errs() << "Find a CallInst: "<< *I <<"\n" << "But can't find which function it calls.\n";        
            
                // if(f->getName()=="__BRICK_SPEC")
                if(f->doesNotReturn()||f->getName()=="__BRICK_SPEC"||f->getName()=="__VERIFIER_error"){
                    continue;
                }
            // **************************Deal with Function isDefined****************************
                if(!f->isDeclaration()) {
                    cfg->stateList[s->ID]=(*s);

                    string callFunc = f->getName();
                    map<string ,int >::iterator it=cfg->funcTime.find(callFunc);
                    int t = 0;
                    if(it==cfg->funcTime.end())
                        cfg->funcTime.insert(pair<string,int>(callFunc,t));
                    else
                        t = ++it->second;

                    readFunc(callFunc, cfg, t);
                    id = cfg->counter_state++;
                    string  str = ConvertToString(cfg->counter_s_state);
                    cfg->counter_s_state++;
                    name = "s"+str;
                    global_CFG.InsertCFGState(id,name,func);

                    string funcName = callFunc;
                    if(t>0)
                        funcName = callFunc+ConvertToString(t);

                    s = new State(false, id, name, func);
                    cfg->stateList.resize(id+1);
                    bool hasFromS = W.InsertCFGLabel(cfg, b, s, func, funcName+"_ret",true);
                    cfg->retVar.pop_back();
                    if(!hasFromS){
                        cfg->counter_state--;
                        cfg->counter_s_state--;
                        return;
                    }
                    else if(s->level>bound){
                        if(cfg->stateList.size()<id)
                            cfg->stateList.resize(id);
                        cfg->stateList[s->ID]=(*s);
                        return;
                    }
                }
            }
        }
        cfg->stateList[s->ID] = (*s);
    }
}

int dfscount = 0;

void ProgramCFG::createSucc(BasicBlock *v){
    (*colors)[v] = GRAY;

    std::vector<CFGNode*> currentNodes ;

    //currentNodes is a node list in which nodes are waiting for find succ.
    currentNodes.push_back(&((*nodes)[v]));//first currentNodes is v

    //errs()<<dfscount++<<" dfs: "<<(*nodes)[v].name<<"\n";

    for(BasicBlock::iterator inst = v->begin(); inst != v->end(); inst ++){
        //errs() << *inst<<"\n";
        if(CallInst* call = dyn_cast<CallInst>(inst)){

            if(isa<UnreachableInst>(++inst)){//exit ,abort ,xalloc_die, program exit.
                //    errs()<< *(--inst)<<"\n"; 
                goto finish;
            }
            --inst; 
            Function *f = call->getCalledFunction();

            //If there is a call asm instruction or function pointer call,
            // the return value of getCalledFunction will be null.
            //So we just ignore it.

            if(!f){ 
//                errs() << "Find a CallInst: "<< *inst <<"\n" << "But can't find which function it calls.\n";
                continue;
            }
            if(f->isDeclaration()) {
//                        errs()<<"isDeclaration " << f->getName() << "\n";
                continue;
            }else{
//               errs() << "hasDefinition " << f->getName() << "\n";
               }
            //only concerns the function in the targetFunctionList
            //    if(targetFunctionList->find(f) == targetFunctionList->end()) continue; 

            //    errs() << "find a call : "<< f->getName() << "\n "; 

            BasicBlock *entry = &f->getEntryBlock(); 
            CFGNode *entryNode =  &((*nodes)[entry]);//f's EntryBlock 
            while(!currentNodes.empty()){
                //link succ and prev to each other
                currentNodes.back()->addSucc(entryNode);
                entryNode->addPrev(currentNodes.back());
                currentNodes.pop_back();
            }

            if((*colors)[entry] == WHITE){//dfs
                createSucc(entry);
            }

            for(std::vector<BasicBlock*>::iterator ret= (*retBlocks)[f].begin();
                    ret != (*retBlocks)[f].end(); 
                    ret++){
                currentNodes.push_back(&((*nodes)[*ret]));
            }
        }
    }
    //assert(currentNodes.size()==1);
    while(!currentNodes.empty()){
        CFGNode* current = currentNodes.back();
        currentNodes.pop_back();
        for(succ_iterator succ = succ_begin(v),end = succ_end(v);
                succ != end;
                succ++){
            CFGNode *succNode = &((*nodes)[*succ]);
            current->addSucc(succNode);
            succNode->addPrev(current);
            if((*colors)[*succ] == WHITE){
                createSucc(*succ);
            }
        }
    }
finish:

    //errs()<<"dfs back\n";

    (*colors)[v] = BLACK;
}


//test programCFG,CHECK THE program cfg 
void ProgramCFG::bfs(CFGNode *r){
    if (r == NULL) return; 
    deque<CFGNode*> q;
    (*colors)[r->bb] = GRAY;
    q.push_front(r);
    errs() <<"WHITE:"<<WHITE<<"BLACK:"<<BLACK<<"GRAY:"<<GRAY<<"\n";
    while(!q.empty()){
        r = q.back();
        q.pop_back();
        errs() << r->name<<"\n  succ: {";
        Succ *child = r->getFirstSucc();
        while(child){
            errs()<< child->v->name<<"("<<(*colors)[child->v->bb]<<"), ";
            if((*colors)[child->v->bb] == WHITE){//not visit
                //errs() << "add: "<<child->v->name;
                (*colors)[child->v->bb] = GRAY;
                q.push_front(child->v);
            }
            child = child->nextSucc;
        }
        (*colors)[r->bb] = BLACK;
        errs() << "}\n  prev: { ";
        Prev *prev = r->getFirstPrev();
        while(prev){
            errs() << prev -> v->name << "(" << (*colors)[prev->v->bb] << "), ";
            prev = prev->nextPrev;
        }
        errs() << "}\n";

    }
}


