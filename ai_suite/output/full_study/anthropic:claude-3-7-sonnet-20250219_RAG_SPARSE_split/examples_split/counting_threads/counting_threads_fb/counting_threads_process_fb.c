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


// TODO: make this function pass the verification
void process(int n)
    //@ requires cell |-> ?v &*& 0 <= n;
    //@ ensures cell |-> v;
{
    //@ start_counting(integer, &cell);
    
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    //@ malloc_block_pointers(threads, n);
    
    for (int i = 0; i < n; i++)
        //@ invariant threads[0..i] |-> ?ts &*& malloc_block_pointers(threads, n) &*& counting(integer, &cell, i, v) &*& 0 <= i &*& i <= n;
    {
        //@ real f = create_ticket(integer, &cell);
        //@ close thread_run_pre(m)(0, unit);
        struct thread *t = thread_start_joinable(m, 0);
        threads[i] = t;
        //@ close thread_info(t);
    }
    
    for (int i = 0; i < n; i++)
        //@ invariant threads[0..n] |-> ?ts &*& malloc_block_pointers(threads, n) &*& counting(integer, &cell, n-i, v) &*& 0 <= i &*& i <= n &*& foreach(take(i, ts), thread_info);
    {
        struct thread *t = threads[i];
        //@ open thread_info(t);
        thread_join(t);
        //@ open thread_run_post(m)(0, _);
        //@ destroy_ticket(integer, &cell);
    }
    
    //@ stop_counting(integer, &cell);
    free(threads);
}