#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = integer(cell, value) &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = integer(cell, value);


typedef void thread_run/*@(predicate(void *) pre, predicate() post)@*/(void *data);
    //@ requires pre(data);
    //@ ensures post();


// TODO: make this function pass the verification
struct thread *thread_start(void *run, void *data);
    //@ requires [_]is_thread_run(run, ?pre, ?post) &*& pre(data);
    //@ ensures thread(result, post);

