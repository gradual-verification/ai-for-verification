#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = *cell |-> value &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = *cell |-> value;

/**
 * The rand() function is not defined in the provided headers, but is used in the
 * examples. We declare it here with a contract that reflects its non-deterministic
 * nature, allowing it to be used in verified code.
 */
int rand();
    //@ requires true;
    //@ ensures true;

// This function is implemented to return a non-deterministic integer.
int read_int()
    //@ requires true;
    //@ ensures true;
{
    return rand();
}
