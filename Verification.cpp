#include "Verification.h"
#include "time.h"
#include "float.h"
using namespace std;
//add constraint to empty vector  0==0

/*******************************class BoundedVerification****************************************/
BoundedVerification::BoundedVerification(CFG* aut, int bound, vector<int> target, double pre, DebugInfo *dbg, int outMode){
    this->cfg=aut;
    this->bound=bound;
    this->target=target;
    this->precision=pre;
    this->dbg=dbg;
    this->outMode = outMode;
    solver_time = 0;
    result = false;
    reachEnd = false;
    num_of_path=0;
    bool isLinear = cfg->isLinear();
    if(isLinear){
        verify = new LinearVerify(dbg, outMode);
    }
    else{
        verify = new UnlinearVerify(precision, dbg, outMode);
    }
}

BoundedVerification::~BoundedVerification(){
    delete verify;
    verify = NULL;
    dbg = NULL;
    cfg = NULL;
    target.clear();
    path.clear();
    witPath.clear();
}

string get_name(CFG *cfg,vector<int> path){
    string name="";
    for(unsigned i=0;i<path.size();i++){
        if(i%2==0){
        name +=cfg->getNodeName(path[i]);
        if(i != path.size()-1)
          name += "^";
        }
    }
    return name;
}

void BoundedVerification::DFS(int intbound,int bound,int start, int end){
    if(bound==0||result==true)
        return;
    
    reachEnd = false;
    int reduntsize=path.size()-2*(intbound-bound);
    if(reduntsize!=0){
        int temp=path.back();
        for(int m=0;m<reduntsize+1;m++)
            path.pop_back();
        path.push_back(temp);
    }

    path.push_back(start);
    
    if(start==end){
        reachEnd = true;
        target_name=cfg->getNodeName(end);
    }

    if(verify->check(cfg, path)){   //the path is feasible, terminate
        num_of_path++;
        if(reachEnd){
            reachPath=get_name(cfg,path);
            for(unsigned i=0;i<path.size();i++){
                witPath.push_back(path[i]);
            }
            result = true;
            return;
        }
        else {
            for(unsigned int i=0;i<cfg->searchState(start)->transList.size();i++){
                State *s = cfg->searchState(start)->transList[i]->toState;
                if(s==NULL) continue;
                path.push_back(cfg->searchState(start)->transList[i]->ID);
                DFS(intbound,bound-1,s->ID,end);
            }
        }
    }

}

/* Bounded reachability analysis return false:unreachable true:reachable */

bool BoundedVerification::check(string check){
//    cfg->print();

    int line;

    encode_graph();    

    if(outMode!=0)
        errs()<<"#targetsize:\t"<<target.size()<<"\n";
    if(target.size()==0){
        errs()<<"Has no exceptions~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n";
        return true;
    }
    
    if(outMode!=0){
        for(int i=0;i<(int)target.size();i++)
            errs()<<"target["<<i<<"]:"<<cfg->stateList[target[i]].name<<"("<<cfg->stateList[target[i]].error<<")\n";
    }
    errs()<<"\n";
    for(int i=0;i<(int)target.size();i++){
        result = false;
        reachEnd = false;
        path.clear();
        witPath.clear();
        if(outMode==1)
            errs()<<"target["<<i<<"]:"<<cfg->stateList[target[i]].name<<"("<<target[i]<<")\n";
        int targetID = target[i];
	if(cfg->isLinear())	
		result=solve(targetID);
	else        
		DFS(bound,bound,cfg->initialState->ID,targetID);
        string name = cfg->stateList[targetID].name;
        if(name.at(0)=='q')
            line = cfg->stateList[targetID].locList[0];
        if(outMode==1)
            errs()<<"target["<<i<<"]:from "<<cfg->initialState->name<<"("<<cfg->initialState->ID<<") to "<<cfg->stateList[targetID].name<<"("<<targetID<<")\n";
        errs()<<cfg->stateList[targetID].error;
        if(cfg->stateList[targetID].error==Spec)
            errs()<<"with expr \""<<check<<"\" ";
        int originLine=line;
        if(check!="")
            originLine=line-1;
        if( result ){
            errs()<<"at line "<<originLine<<" in state "<<target_name<<" is reachable, When\n";
            // verify->print_sol(cfg);
            errs()<<"Number of path checked:"<<num_of_path<<"\n";

            if(outMode==1){
                errs()<<"Witness:\n";
                for(unsigned i=0; i<witPath.size();i++){
                    int id = witPath[i];
                    State *s = cfg->searchState(id);
                    assert(s!=NULL);
                    cerr<<"\t"<<s->name<<":";
                    cerr<<"\tLocLine:";
                    for(unsigned j=0;j<s->locList.size();j++)
                        cerr<<s->locList[j]<<";";
                    cerr<<"\n";
                    if(i<witPath.size()-1){
                        Transition *t = cfg->searchTransition(witPath[++i]);
                        assert(t!=NULL);
                        cerr<<"\t"<<t->name<<"\n";
                    }
                }
            }
        }
        else{
            errs()<<"at line "<<originLine<<" is unreachable under bound "<<bound<<"\n";
            errs()<<"Number of path checked:"<<num_of_path<<"\n";
        }
        if(outMode!=0)
        {
            errs()<<"#Avg_var: "<<dbg->counter_var*1.0/num_of_path<<"\n";
            errs()<<"#Avg_nolinearop: "<<dbg->counter_op*1.0/num_of_path<<"\n";
        }
        double time = verify->getTime();
        solver_time += time;
        errs() << "Solver Time: \t" << ConvertToString(time) << "ms\n\n";
    }

    return result;
}

bool BoundedVerification::solve(int cur_target){

    for(int i=0;i<=bound;i++){
        while(true){
            if(s.solve(var(i,cur_target))){
                num_of_path++;
                vector<int> path=decode_path(cur_target);
                if(verify->check(cfg, path)){   //the path is feasible, terminate
                    reachPath=get_path_name(cfg,path);
                    return true;
                }
                else{                //infeasible, feed the IIS path to the SAT solver
                    //errs()<<"TRY Path: "<<get_path_name(path)<<"\n";
                    block_path(num_of_path,cfg,path);
                }
            }
            else
                break;
        }
    }
    return false;
}


/* extract the infeasible path segement and feed to the SAT solver */
void  BoundedVerification::block_path(int number,CFG *cfg,vector<int> path){
    
    vector<IndexPair> indexs = verify->get_core_index();
//printVector(path);
//printIndex(indexs);
    for(unsigned m=0;m<indexs.size();m++){
        int pathStart = indexs[m].start;
        int pathEnd   = indexs[m].end;
        vector<int> pathsegment;
        for (int i=pathStart;i<pathEnd; i++) {
            pathsegment.push_back(path[2*i]);
            pathsegment.push_back(path[2*i+1]);            
        }
        pathsegment.push_back(path[2*pathEnd]);
        
//errs()<<"IIS Path "<<number<<":"<<get_path_name(cfg,pathsegment)<<"\n\n";    
        int loop = bound-(pathEnd-pathStart);
        for(int i=0;i<=loop;i++){
            Minisat::vec<Minisat::Lit> lits;
            for(unsigned j=0;j<pathsegment.size();j++){
                lits.push(~var(i+j/2,pathsegment[j]));    
            //    errs()<<"v("<<i+j/2<<","<<pathsegment[j]<<")"<<"\n";
            }
            s.addClause(lits);            
        }
    }
}

/*encode the bounded graph structure of LHA into a propositional formula set*/
void BoundedVerification::encode_graph(){
    Minisat::vec<Minisat::Lit> lits;
    //initial condition    
    for(unsigned i=0;i<cfg->stateList.size();i++){
        State* st = &cfg->stateList[i];
        if(st->isInitial)
            s.addClause(var(0,st->ID));
        else
            s.addClause(~var(0,st->ID));
    }

    //not exactly in one location and transition, exclude condition
    for(int k=0;k<=bound;k++){
        for(unsigned i=0;i<cfg->stateList.size();i++){
            for(unsigned j=i+1;j<cfg->stateList.size();j++){
                s.addClause(~var(k,cfg->stateList[i].ID), ~var(k,cfg->stateList[j].ID));
            }
        }
        for(unsigned i=0;i<cfg->transitionList.size();i++){
            for(unsigned j=i+1;j<cfg->transitionList.size();j++){
                s.addClause(~var(k,cfg->transitionList[i].ID), ~var(k,cfg->transitionList[j].ID));
            }
        }
    }
    // transition relation 
    for(unsigned i=0;i<cfg->stateList.size();i++){
        State* st = &cfg->stateList[i];            
        for(int k=0;k<bound;k++){
            Minisat::Lit x=var(k,st->ID);
            if(st->transList.size()==0){
                s.addClause(~x,var(k+1,st->ID));
                for(unsigned j=0;j<cfg->transitionList.size();j++){
                    s.addClause(~x, ~var(k,cfg->transitionList[j].ID));
                }
            }
            else{    
                lits.clear();
                for(unsigned j=0;j<st->transList.size();j++){
                    if(st->transList[j]->toState==NULL) continue;
                    Minisat::Lit next_tran_exp=var(k,st->transList[j]->ID);
                    Minisat::Lit next_state_exp=var(k+1,st->transList[j]->toState->ID);
                    s.addClause(~x, ~next_tran_exp, next_state_exp);
                    lits.push(next_tran_exp);
                }
                lits.push(~x);
                s.addClause(lits);
            }
        }
    }
}

/*
Minisat::vec<Minisat::Lit> BoundedVerification::setTarget(int cur_target){
    //target condition
    Minisat::vec<Minisat::Lit> lits;
    lits.clear();
    for(int i=0;i<=bound;i++)
        lits.push(var(i,cur_target));
    return lits;
}
*/
/* decode a path from a satisfiable model */
vector<int>  BoundedVerification::decode_path(int cur_target){
    assert(s.okay());
    int state_num=cfg->stateList.size()+cfg->transitionList.size();;
    int* path=new int[2*bound+1];
    for (int i=1;i<=state_num*(bound+1); i++) {
        if(s.modelValue(i) == Minisat::l_True){
            int id,loop;
            decode(i,loop,id);
            if(cfg->is_state(id))
                path[2*loop]=id;
            else
                path[2*loop+1]=id;
        }
    }
    vector<int> compress_path;
    for(int i=0;i<2*bound+1;i++){
        compress_path.push_back(path[i]);
        if(path[i] == cur_target)
          break;
    }
    delete[] path;
    return compress_path;
}


string BoundedVerification::get_path_name(CFG *cfg,vector<int> path){
    string name="";
    for(unsigned i=0;i<path.size();i++){
        if(i%2==0){
        name +=cfg->getNodeName(path[i]);
        name+="(";
        for(vector<int>::iterator it=cfg->searchState(path[i])->locList.begin();it<cfg->searchState(path[i])->locList.end();it++){
        name+=intToString(*it);
        if(it+1!=cfg->searchState(path[i])->locList.end()){
           name+=",";
       }
    }
        name+=")";
        if(i != path.size()-1)
          name += "^";
    }
    }
    if(cfg->searchState(path[path.size()-1])->locList.empty()){
        name=name.substr(0,name.length()-5);
    }
    return name;
}
Minisat::Lit BoundedVerification::var(const int loop, const int st){
    int state_num=cfg->stateList.size()+cfg->transitionList.size();;
    int var= state_num*loop+st+1;
    while (var >= s.nVars()-1) s.newVar();
    return Minisat::mkLit(var);
}

void BoundedVerification::decode(int code,int& loop,int& ID){
    code--;
    int state_num=cfg->stateList.size()+cfg->transitionList.size();;
    loop = code/state_num;
    ID = code%state_num;
}

