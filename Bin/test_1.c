#include <assert.h>
#include <math.h>

int main(){
	unsigned x,y,z;
	x = y - 100000000000;
	if(y>1)
		z=x/y;
	else if(y>=-1)
		z=asin(y);
	else
		z=sqrt(-y);
	return 0;
}
