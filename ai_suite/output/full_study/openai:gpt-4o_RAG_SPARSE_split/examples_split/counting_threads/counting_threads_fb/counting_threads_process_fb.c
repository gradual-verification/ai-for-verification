#include "stdlib.h"
#include "threading.h"

// Global variable
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
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    //@ close pointers(threads, n, _);
    //@ close malloc_block_pointers(threads, n);

    for (int i = 0; i < n; i++)
        //@ invariant pointers(threads, n, ?ts) &*& 0 <= i &*& i <= n &*& malloc_block_pointers(threads, n);
    {
        struct thread *t = thread_start_joinable(m, 0);
        threads[i] = t;
        //@ close thread_info(t);
    }

    for (int i = 0; i < n; i++)
        //@ invariant pointers(threads, n, ?ts) &*& foreachp(ts, thread_info) &*& 0 <= i &*& i <= n &*& malloc_block_pointers(threads, n);
    {
        struct thread *t = threads[i];
        //@ open thread_info(t);
        thread_join(t);
    }
    //@ open pointers(threads, n, _);
    free(threads);
}