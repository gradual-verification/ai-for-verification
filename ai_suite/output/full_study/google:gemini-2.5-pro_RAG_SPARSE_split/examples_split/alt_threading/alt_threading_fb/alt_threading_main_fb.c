#include "stdlib.h"
#include "assert.h"
#include "limits.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(void *data) = *cell |-> value &*& data == cell;
//@ predicate_ctor integer2(int *cell, int value)() = *cell |-> value;


typedef void thread_run/*@(predicate(void *) pre, predicate() post)@*/(void *data);
    //@ requires pre(data);
    //@ ensures post();


struct thread *thread_start(void *run, void *data);
    //@ requires [_]is_thread_run(run, ?pre, ?post) &*& pre(data);
    //@ ensures thread(result, post);


void thread_join(struct thread *thread);
    //@ requires thread(thread, ?post);
    //@ ensures post();


void increment(int *cell)
    //@ requires *cell |-> ?value;
    //@ ensures *cell |-> value + 1;
{
    (*cell)++;
}


int read_int();
    //@ requires true;
    //@ ensures true;


// TODO: make this function pass the verification
int main()
    //@ requires true;
    //@ ensures true;
{
    int *cell = malloc(sizeof(int));
    if (cell == 0) abort();
    int n = read_int();
    if (n >= INT_MAX) {
        abort();
    }
    *cell = n;
    struct thread *t = thread_start(increment, cell);
    thread_join(t);
    
    int n1 = *cell;
    free(cell);
    assert(n1 == n + 1);
    return 0;
}