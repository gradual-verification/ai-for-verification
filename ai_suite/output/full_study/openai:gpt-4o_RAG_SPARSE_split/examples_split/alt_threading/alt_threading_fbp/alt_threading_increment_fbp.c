#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = integer(cell, value) &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = integer(cell, value);

// TODO: make this function pass the verification
void increment(int *cell)
    //@ requires integer(cell, ?value) &*& value >= INT_MIN &*& value < INT_MAX;
    //@ ensures integer(cell, value + 1);
{
    //@ produce_limits(value);
    if (value == INT_MAX) abort(); // Prevent overflow
    (*cell)++;
}