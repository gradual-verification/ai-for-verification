// Includes necessary libraries
//@ #include "arrays.gh"
//@ #include "counting.gh"
#include "malloc.h"
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

void process(int n)
    //@ requires integer(&cell, ?v) &*& 0 <= n &*& 0 <= n * sizeof(struct thread *) &*& n * sizeof(struct thread *) <= INT_MAX;
    //@ ensures integer(&cell, v);
{
    
    // Allocate memory for thread pointers
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();

    // Start threads
    for (int i = 0; i < n; i++)
    {
        struct thread *t = thread_start_joinable(m, 0);
        threads[i] = t; // <-- Changed from *(threads + i) = t; to threads[i] = t;
    }
    
    // Join threads
    for (int i = 0; i < n; i++)
    {
        struct thread *t = threads[i]; // <-- Changed from *(threads + i) to threads[i]
        thread_join(t);
    }
    free(threads);
}