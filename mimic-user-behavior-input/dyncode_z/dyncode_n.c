// verifast_annotation_char:#

#include <stdbool.h>
#include "assert.h"
#include "malloc.h"
#include "stdlib.h"

/*@ This is ignored by VeriFast. @*/
typedef int sillyfunc/*#(predicate() p)#*/();
    //# requires [?f]p();
    //# ensures [f]p() &*& result == 1;

//# predicate_ctor chars_ctor(char *start, list<char> contents)() = chars(start, _, contents);
/*
  Natural Language Specification:
  - Description: Entry point of the program. Allocates memory for machine code, sets up a function pointer to this code, executes the code, and frees the allocated memory. Asserts that the function result is 1.
  - Parameters: None.
  - Requires: True.
  - Ensures: True.
*/
int main() //# : main
   
{
    char *code = malloc(4);
    if (code == 0) abort();
    sillyfunc *funcptr = 0;
    int funcresult = 0;
    
   
    
    *(code + 0) = 0x33;
    *(code + 1) = (char)0xC0;
    *(code + 2) = 0x40;
    *(code + 3) = (char)0xC3;
    
   
    funcptr = (void *)code;
    {
       
    }
    funcresult = funcptr();
   
    free(code);
    
    assert(funcresult == 1);
    
    return 0;
}
