// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*@

predicate_family_instance thread_run_pre(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);
predicate_family_instance thread_run_post(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);

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
    //@ requires integer(&cell, ?v) &*& 0 <= n &*& 0 <= n * sizeof(struct thread *) &*& n * sizeof(struct thread *) <= INT_MAX;
    //@ ensures integer(&cell, v);
{
    //@ start_counting(integer, &cell);
    
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    //@ malloc_block_pointers(threads, n);

    for (int i = 0; i < n; i++)
        //@ invariant counting(integer, &cell, i, v) &*& malloc_block_pointers(threads, n) &*& pointers(threads, i, ?ts) &*& 0 <= i &*& i <= n &*& foreachp(ts, thread_info);
    {
        //@ real frac = create_ticket(integer, &cell);
        struct thread *t = thread_start_joinable(m, 0);
        threads[i] = t;
        //@ close thread_info(t);
    }
    
    for (int i = 0; i < n; i++)
        //@ invariant counting(integer, &cell, n-i, v) &*& malloc_block_pointers(threads, n) &*& pointers(threads, n, ?ts) &*& 0 <= i &*& i <= n &*& foreachp(drop(i, ts), thread_info);
    {
        struct thread *t = threads[i];
        //@ open thread_info(t);
        thread_join(t);
        //@ destroy_ticket(integer, &cell);
    }
    
    //@ stop_counting(integer, &cell);
    free(threads);
}