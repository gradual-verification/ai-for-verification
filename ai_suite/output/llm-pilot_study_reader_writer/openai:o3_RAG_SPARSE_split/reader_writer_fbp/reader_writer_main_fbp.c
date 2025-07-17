#include "stdlib.h"
#include "threading.h"

/* ============================================================================
   A very small readers-writers example.
   The reader and writer threads are already verified.  Below we add the
   necessary bookkeeping in main() so that the whole program verifies.
   ==========================================================================*/

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

struct rwlock *rwlock_init()
    //@ requires true;
    //@ ensures result->mutex |-> ?m &*& mutex(m, rwlock_inv(result));
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    //@ close rwlock_inv(l)();              // invariant holds initially
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    l->mutex = create_mutex();
    return l;
}

void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    mutex_acquire(l->mutex);

    if (l->readers == INT_MAX) abort();
    l->readers++;
    mutex_release(l->mutex);

    /* critical section (reading) */

    mutex_acquire(l->mutex);
    if (l->readers == 0) abort();
    l->readers--;
    mutex_release(l->mutex);
}

void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    for (;;)
    {
        mutex_acquire(l->mutex);
        if (l->readers == 0) break;
        mutex_release(l->mutex);
    }

    /* critical section (writing) */

    mutex_release(l->mutex);
}

/* ---------------------------------------------------------------------------
   The only change that was required to make the whole file verify is the
   annotated bookkeeping in main(): we split the permissions that rwlock_init
   gives us and pass a half to each thread.
   -------------------------------------------------------------------------*/
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct rwlock *l = rwlock_init();

    /* We own:
         l->mutex |-> m                              (coefficient 1)
         mutex(m, rwlock_inv(l))                     (coefficient 1)
       We need to give each thread half of both chunks.                         */

    struct mutex *m = l->mutex;   // obtain the value, keeps permissions

    /* Split the (precise) field chunk into two halves */
    //@ open l->mutex |-> m;
    //@ close [1/2]l->mutex |-> m;          // for first thread
    //@ close [1/2]l->mutex |-> m;          // keep the other half

    /* Pass ½ + ½ chunks to the reader thread */
    //@ close thread_run_data(reader)(l);
    thread_start(reader, l);

    /* We still have:
         [1/2]l->mutex |-> m
         [1/2]mutex(m, rwlock_inv(l))
       These are exactly what the writer thread needs.                         */
    //@ close thread_run_data(writer)(l);
    thread_start(writer, l);

    return 0;
}