// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.hh"
#include "threading.h"

static int cell;

/*@

predicate_family_instance thread_run_pre(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);
predicate_family_instance thread_run_post(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);

predicate thread_info(struct thread *t) = thread(t, m, _, _);

predicate joined_threads_post(int k) =
    k == 0 ?
        emp
    :
        ticket(integer, &cell, ?f) &*& [f]integer(&cell, _) &*& joined_threads_post(k - 1);

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
    
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    //@ chars__to_pointers_(threads, n);
    //@ divrem_intro(n * sizeof(struct thread *), sizeof(struct thread *), n, 0);
    //@ close malloc_block_pointers(threads, n);

    //@ start_counting(integer, &cell);

    for (int i = 0; i < n; i++)
    /*@
        invariant 0 <= i &*& i <= n &*&
                  counting(integer, &cell, i, v) &*&
                  pointers(threads, i, ?ts) &*&
                  foreach(ts, thread_info) &*&
                  pointers_(threads + i, n - i, _) &*&
                  malloc_block_pointers(threads, n);
    @*/
    {
        //@ create_ticket(integer, &cell);
        //@ close thread_run_pre(m)(0, unit);
        struct thread *t = thread_start_joinable(m, 0);
        //@ close thread_info(t);
        threads[i] = t;
    }
    
    //@ list<struct thread *> ts = ?ts_final;
    //@ close joined_threads_post(0);
    for (int i = 0; i < n; i++)
    /*@
        invariant 0 <= i &*& i <= n &*&
                  counting(integer, &cell, n, v) &*&
                  pointers(threads, n, ts) &*&
                  foreach(drop(i, ts), thread_info) &*&
                  joined_threads_post(i) &*&
                  malloc_block_pointers(threads, n);
    @*/
    {
        struct thread *t = threads[i];
        //@ open foreach(drop(i, ts), thread_info);
        thread_join(t);
        //@ open thread_run_post(m)(0, _);
        //@ close joined_threads_post(i + 1);
    }
    
    for (int i = 0; i < n; i++)
    /*@
        invariant 0 <= i &*& i <= n &*&
                  counting(integer, &cell, n - i, v) &*&
                  joined_threads_post(n - i) &*&
                  pointers(threads, n, ts) &*&
                  malloc_block_pointers(threads, n);
    @*/
    {
        //@ open joined_threads_post(n - i);
        //@ destroy_ticket(integer, &cell);
    }

    //@ stop_counting(integer, &cell);
    
    //@ pointers_to_pointers_(threads);
    //@ pointers__to_chars_(threads);
    free(threads);
}