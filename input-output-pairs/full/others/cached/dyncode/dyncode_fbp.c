#include <stdbool.h>
#include "assert.h"
#include "malloc.h"
#include "stdlib.h"

typedef int sillyfunc/*@(predicate() p)@*/();
    //@ requires [?f]p();
    //@ ensures [f]p() &*& result == 1;

//@ predicate_ctor chars_ctor(char *start, list<char> contents)() = chars(start, _, contents);

int main()
    //@ requires true;
    //@ ensures true;
{
    char *code = malloc(4);
    if (code == 0) abort();
    sillyfunc *funcptr = 0;
    int funcresult = 0;
    
    // x86 machine code:
    // 33 C0   xor eax, eax
    // 40      inc eax
    // C3      ret
    
    *(code + 0) = 0x33;
    *(code + 1) = (char)0xC0;
    *(code + 2) = 0x40;
    *(code + 3) = (char)0xC3;
    
    funcptr = (void *)code;

    funcresult = funcptr();

    free(code);
    
    assert(funcresult == 1);
    
    return 0;
}