#include <iostream>
#include <stdlib.h>
#include <string.h>
#include <sstream>
#include <stdio.h>
using namespace std;

string split(string filename);
void printUsage();
void compile(string name, int o);
void opt(string name, int b, double p, int m, char* f, char* e, int o);
void addExpr(string name, string expr);
string inttostring(const int i);
string doubletostring(const double d);


int main(int argc, char* argv[]){
    if(argc < 6){
        printUsage();
        exit(1);
    }
  
    //Process the flags
    string filename(argv[1]);
    cout << "<" << filename << "> \n";
    char* expression = NULL;
    char* func = NULL;
    int bound=0;
    int line=-1;
    double precision=0.01;
    int mode = 0;
    bool mode_a=false;
    bool mode_d=false;
    int output=0;
    for(int i = 2; i < argc; i ++){
        if(argv[i][0] == '-' && strlen(argv[i]) == 2){
            if(argv[i][1] == 'f'){
                func = argv[i+1]; 
                i ++;
            }
            else if(argv[i][1] == 'b'){
                bound = atoi(argv[i+1]);
                i ++;
            }
            else if(argv[i][1] == 'p'){
                precision = atof(argv[i+1]);
                i ++;
            }
            else if(argv[i][1] == 'l'){
                line = atoi(argv[i+1]);
                i ++;
            }
            else if(argv[i][1] == 's'){
                expression = argv[i+1];
                i ++;
            }
            else if(argv[i][1] == 'a'){
                mode_a = true;
            }
            else if(argv[i][1] == 'd'){
                mode_d = true;
            }
            else if(argv[i][1] == 'o'){
                output=1;
            }
            else if(argv[i][1] == 't'){
                output=2;
            }
            else{
                printUsage();
                exit(1); 
            }
        }
    }
    if(func==NULL||bound==0){
        printUsage();
        exit(1);
    }
    if (mode_a&&!mode_d)
        mode = 1;
    else if(mode_d&&!mode_a)
        mode = 2;
    if(expression!=NULL){
        if(line==-1){
            printUsage();
            exit(1);
        }
        else{
            string BRICKname="BRICK_"+filename;
            string exec="sed -e \'1s/^/void __BRICK_SPEC(int x){}\\n/\' -e \'";
            exec+=inttostring(line)+"s/$/__BRICK_SPEC("+string(expression)+");/\' ";
            exec+=filename+" > "+BRICKname;
//            "sed -e \'6s/^/{/' -e '6s/$/void __BRICK_SPEC(int);__BRICK_SPEC(1);}/' test.txt > sed.txt"
            int response = system(exec.c_str());
            filename=BRICKname;
        }
    }

    string name = split(filename);
    compile(name, output);
    opt(name, bound, precision, mode, func, expression, output);
    return 0;
}

void printUsage(){
    cout << "Usage: BRICK filename -f <func> -b <bound> -p <precision> [-options]" << endl;
    cout << "[-options]:" << endl;
    cout<<"\t-l <line> (-s <expr>)\tspecify lineNo (and expression) to check on"<<endl;
    cout<<"\t-o\t\tBRICK display CFG and constraints while checking"<<endl;
    cout<<"\t-t\t\tBRICK display test informations while checking"<<endl;
    cout<<"\t-a\t\tset mode in which BRICK check assert only"<<endl;
    cout<<"\t-d\t\tset mode in which BRICK check domain error only"<<endl;
}

void compile(string name, int o){
    string cflags = "-emit-llvm -g ";
    string command = "clang -c " + cflags + name + ".c " + "-o "+ name + ".bc";
    if(o)    
       cout << command<<endl;
    int response = system(command.c_str());
    return;
}

// convert integer to char, but only up to 256 digits!
string inttostring(const int i)
{
  char chr[256];
  string str;
  sprintf(chr,"%i",i);
  str=chr;
  return str;
}
 // convert integer to char, but only up to 256 digits!
string doubletostring(const double d)
{
  char chr[256];
  string str;
  sprintf(chr,"%g",d);
  str=chr;
  return str;
}

void opt(string name, int b, double p, int m, char* f, char* e, int o){
    string bound = "-bound=" + inttostring(b);
    string precision = "-pre=" + doubletostring(p);
    string mode = "-mode=" + inttostring(m);
    string func = "-func=" + string(f);
    string output = "-output=" + inttostring(o);
    string expr = "";
    if(e != NULL)
        expr += ("-expression=\""+string(e)+"\"");
    string command = "opt -load buildCFG.so -load libz3.so -load libminisat.so "
    "-load libcapd.so -load libibex.so -load libdreal.so "
    "-buildCFG "+bound+" "+precision+" "+mode+" "+func+" "+output+" "+expr+"<"+name+".bc>"+" "+name+"buildCFG.bc";
	// g++ test_dreal.c -o test_dreal_inf -ldreal -libex -lClpSolver -lClp -lCoinUtils -lm -lcapd -lnlopt -lprim -lpthread -lstdc++ 
    if(o)    
	   cout << command<<endl;
    int response = system(command.c_str());
}

string split(string filename){
    unsigned i;
    for(i = 0; i < filename.length(); i ++){
        if(filename.at(i) == '.')
            break;
    }
    return filename.substr(0,i);
}
