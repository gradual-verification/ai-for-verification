#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = integer(cell, value) &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = integer(cell, value);


// TODO: make this function pass the verification
void thread_join(struct thread *thread);
    //@ requires thread(thread, ?post);
    //@ ensures post();

