#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = *cell |-> value &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = *cell |-> value;

// TODO: make this function pass the verification
typedef void thread_run/*@(predicate(void *) pre, predicate() post)@*/(void *data);
    //@ requires pre(data);
    //@ ensures post();

/*@
// Define a predicate family for thread_run_pre and thread_run_post
predicate_family thread_run_pre(void *thread_run)(void *data, any info);
predicate_family thread_run_post(void *thread_run)(void *data, any info);

// Define the contract for thread_start_joinable
predicate thread_start_joinable_pre(thread_run *run, void *data, any info) = 
    is_thread_run(run) == true &*& thread_run_pre(run)(data, info);

predicate thread_start_joinable_post(struct thread *thread, void *run, void *data, any info) = 
    thread(thread, run, data, info);
@*/

struct thread *thread_start_joinable(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_pre(run)(data, ?info);
    //@ ensures thread(result, run, data, info);

void thread_join(struct thread *thread);
    //@ requires thread(thread, ?run, ?data, ?info);
    //@ ensures thread_run_post(run)(data, info);