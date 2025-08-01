#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = *cell |-> value &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = *cell |-> value;


// TODO: make this function pass the verification
int read_int();
    //@ requires true;
    //@ ensures true;

