#include "stdlib.h"
#include "threading.h"

// Global variable
static int cell;

//@ predicate cell_invariant() = integer(&cell, _);

void m(void *data) //@ : thread_run_joinable
    //@ requires cell_invariant();
    //@ ensures cell_invariant();
{
    //@ open cell_invariant();
    int x = cell;
    //@ close cell_invariant();
}

// TODO: make this function pass the verification
void process(int n)
    //@ requires 0 <= n &*& cell_invariant();
    //@ ensures cell_invariant();
{
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    //@ close pointers(threads, n, _);

    for (int i = 0; i < n; i++)
        //@ invariant pointers(threads, n, ?ts) &*& 0 <= i &*& i <= n &*& cell_invariant();
    {
        struct thread *t = thread_start_joinable(m, 0);
        //@ assert thread(t, m, 0, _);
        threads[i] = t;
        //@ pointers_split(threads, i);
        //@ close pointers(threads + i, 1, cons(t, nil));
        //@ pointers_join(threads);
    }

    for (int i = 0; i < n; i++)
        //@ invariant pointers(threads, n, ?ts) &*& 0 <= i &*& i <= n &*& foreachp(take(i, ts), (thread_run_post)(m, 0));
    {
        struct thread *t = threads[i];
        thread_join(t);
        //@ open thread_run_post(m)(0, _);
        //@ pointers_split(threads, i);
        //@ close pointers(threads + i, 1, _);
        //@ pointers_join(threads);
    }
    //@ open pointers(threads, n, _);
    free(threads);
}

//@ predicate cell_invariant() = integer(&cell, _);