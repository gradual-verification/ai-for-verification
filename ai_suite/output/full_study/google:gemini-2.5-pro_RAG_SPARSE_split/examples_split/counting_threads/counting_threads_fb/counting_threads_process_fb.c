// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*@

predicate_family_instance thread_run_pre(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);
predicate_family_instance thread_run_post(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);

predicate thread_info(struct thread *t) = thread(t, m, 0, unit);

@*/


void m(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(m)(data, ?info);
    //@ ensures thread_run_post(m)(data, info);
{
    //@ open thread_run_pre(m)(data, info);
    int x = cell;
    //@ close thread_run_post(m)(data, info);
}


// TODO: make this function pass the verification
void process(int n)
    //@ requires cell |-> ?v &*& 0 <= n;
    //@ ensures cell |-> v;
{
    //@ start_counting(integer, &cell);
    
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    //@ chars__to_pointers_(threads, n);

    for (int i = 0; i < n; i++)
        /*@
        invariant 0 <= i &*& i <= n &*&
                  counting(integer, &cell, i, v) &*&
                  pointers(threads, i, ?ts) &*& foreach(ts, thread_info) &*&
                  pointers_(threads + i, n - i, _) &*&
                  malloc_block_pointers(threads, n);
        @*/
    {
        //@ real f = create_ticket(integer, &cell);
        //@ close thread_run_pre(m)(0, unit);
        struct thread *t = thread_start_joinable(m, 0);
        //@ close thread_info(t);
        threads[i] = t;
    }
    
    //@ open pointers_(threads + n, 0, _);
    
    for (int i = 0; i < n; i++)
        /*@
        invariant 0 <= i &*& i <= n &*&
                  counting(integer, &cell, n - i, v) &*&
                  pointers(threads, n, ?ts) &*&
                  foreach(drop(i, ts), thread_info) &*&
                  malloc_block_pointers(threads, n);
        @*/
    {
        struct thread *t = threads[i];
        //@ open foreach(drop(i, ts), thread_info);
        //@ open thread_info(nth(i, ts));
        thread_join(t);
        //@ open thread_run_post(m)(0, unit);
        //@ destroy_ticket(integer, &cell);
    }
    
    //@ open foreach(nil, thread_info);
    
    //@ pointers_to_pointers_(threads);
    //@ pointers__to_chars_(threads);
    free(threads);
    
    //@ stop_counting(integer, &cell);
}