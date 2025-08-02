#include "stdlib.h"

//@ predicate integer(int *p; int v) = *p |-> v;

// TODO: make this function pass the verification
void increment(int *cell)
    //@ requires integer(cell, ?value);
    //@ ensures integer(cell, value + 1);
{
    //@ open integer(cell, value);
    (*cell)++;
    //@ close integer(cell, value + 1);
}