#!/bin/bash
echo "Building Checker~~~~~~~~~~~~~~~~~~~~~~~~"
make
myPath="Bin"
if [ ! -d "$myPath" ]; then
	mkdir "$myPath"
fi 
sudo install ../../../Release+Asserts/lib/buildCFG.so /usr/local/lib
g++ main.cpp -o Bin/BRICK
sudo chmod -R 777 Bin
echo "Building finished!-----------------------Start run program in Directory Bin"

