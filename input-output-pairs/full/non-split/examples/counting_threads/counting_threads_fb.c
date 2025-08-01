// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*@

predicate_family_instance thread_run_pre(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& cell |-> _;
predicate_family_instance thread_run_post(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& cell |-> _;

predicate thread_info(struct thread *t) = thread(t, m, _, _);

@*/

void m(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(m)(data, ?info);
    //@ ensures thread_run_post(m)(data, info);
{
    int x = cell;
}

void process(int n)
    //@ requires cell |-> ?v &*& 0 <= n;
    //@ ensures cell |-> v;
{
    
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();

    for (int i = 0; i < n; i++)
    {
        struct thread *t = thread_start_joinable(m, 0);
        threads[i] = t;
    }
    
    for (int i = 0; i < n; i++)
    {
        struct thread *t = threads[i];
        thread_join(t);
    }
    free(threads);
}