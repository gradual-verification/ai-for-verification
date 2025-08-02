#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = *cell |-> value &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = *cell |-> value;

int read_int()
    //@ requires true;
    //@ ensures integer(result, _);
{
    int *result = malloc(sizeof(int));
    if (result == 0) abort();
    *result = 0; // Initialize with a default value
    //@ close integer(result, 0);
    return result;
}