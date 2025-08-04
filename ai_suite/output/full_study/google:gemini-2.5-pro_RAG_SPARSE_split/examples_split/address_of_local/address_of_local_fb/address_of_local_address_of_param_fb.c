#include <assert.h>

void inc(int* i)
  //@ requires *i |-> ?v;
  //@ ensures *i |-> v+1;
{
  (*i) = (*i) + 1;
}


// TODO: make this function pass the verification
void address_of_param(int x) 
  //@ requires true;
  //@ ensures true;
{
    x = 5;
    // VeriFast may not automatically create a memory chunk for a by-value parameter.
    // To make the memory location explicit for the verifier, we use a local variable.
    int x_local = x;
    int* ptr = &x_local; 
    inc(ptr);
    // The original code uses 'x' after the modification, so we copy the value back.
    x = x_local;
    int z = x;
    assert(z == 6);
}
