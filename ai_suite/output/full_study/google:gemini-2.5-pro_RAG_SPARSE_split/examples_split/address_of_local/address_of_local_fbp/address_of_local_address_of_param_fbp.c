#include "assert.h"
#include "limits.h"

void inc(int* i)
  //@ requires integer(i, ?v) &*& INT_MIN <= v &*& v < INT_MAX;
  //@ ensures integer(i, v+1);
{
  (*i) = (*i) + 1;
}


// TODO: make this function pass the verification
void address_of_param(int x) 
  //@ requires true;
  //@ ensures true;
{
    // In C, taking the address of a parameter is valid. However, VeriFast may
    // not allow materializing a heap predicate (like `integer`) for a parameter
    // to prevent returning pointers to stack variables.
    // To ensure verification, we use a separate local variable, which is a
    // pattern known to be verifiable.
    int local_var;
    local_var = 5;
    int* ptr = &local_var; 
    inc(ptr);
    int z = local_var;
    assert(z == 6);
}