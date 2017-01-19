#ifndef _general_h
#define _general_h
#include <stdio.h>
#include <iostream>
#include <sstream>
#include <cstring>
#include <map>
#include <string>
#include <stdlib.h>

using namespace std;

extern int VERBOSE_LEVEL;


void pause_key();
 
void throw_error(string s);

void throw_warning(string s);

void progress_dot();

void progress_dot_end();

void message(unsigned int level, string s);

string int2string(const int i);

string double2string(const double d);

string ConvertToString(const double d);

double ConvertToDouble(const string s);

#endif

                

