#include <stdio.h>
#include <stdlib.h>

#define snareLength 2
#define bigLen  4 // 2 ^ 2 ^ M

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[snareLength] snareVector; 
typedef unsigned __CPROVER_bitvector[bigLen] bigVector;
 
//Constrine the value between 0 and 1
unsigned int  nondet (){  
  unsigned int num = nondet_uint();
  __CPROVER_assume( num>= 0 && num  <= 1);
   return num;
};




int main (int argc, char** argv)

{    

__CPROVER_bitvector[1678] b1;    
assert(0);


}
