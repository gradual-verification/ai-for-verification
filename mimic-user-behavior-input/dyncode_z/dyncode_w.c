// verifast_annotation_char:#

#include <stdbool.h>
#include "assert.h"
#include "malloc.h"
#include "stdlib.h"



int main() //# : main
    //# requires true;
    //# ensures true;
{
    char *code = malloc(4);
    if (code == 0) abort();
    sillyfunc *funcptr = 0;
    int funcresult = 0;
    
   
    
    *(code + 0) = 0x33;
    *(code + 1) = (char)0xC0;
    *(code + 2) = 0x40;
    *(code + 3) = (char)0xC3;
    

  
    funcresult = funcptr();
    
    free(code);
    
    assert(funcresult == 1);
    
    return 0;
}
