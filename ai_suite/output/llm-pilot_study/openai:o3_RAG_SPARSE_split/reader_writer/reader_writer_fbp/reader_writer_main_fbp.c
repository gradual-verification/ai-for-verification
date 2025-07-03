#include "stdlib.h"
#include "threading.h"
#include <limits.h>

/* Readers–writers lock verified with VeriFast                                       */
/* -------------------------------------------------------------------------------- */

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
// Invariant owned by the mutex of the readers–writers lock
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*&                       // current reader count
    r >= 0 &*&                                  // never negative
    malloc_block_rwlock(l);                     // memory of the lock structure

// Predicate family instances that describe what a reader/writer thread needs
predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

/* -------------------------------------------------------------------------------- */
/*  Initialisation                                                                  */
/* -------------------------------------------------------------------------------- */

struct rwlock *rwlock_init()
    //@ requires true;
    //@ ensures result->mutex |-> ?m &*& mutex(m, rwlock_inv(result));
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();

    l->readers = 0;

    /* Close the lock invariant and hand it to the mutex that is about to be
       created, together with the obligatory create-mutex ghost argument.     */
    //@ close rwlock_inv(l)();
    //@ close create_mutex_ghost_arg(rwlock_inv(l));
    struct mutex *m = create_mutex();
    l->mutex = m;

    return l;
}

/* -------------------------------------------------------------------------------- */
/*  Reader                                                                          */
/* -------------------------------------------------------------------------------- */

void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    //@ open thread_run_data(reader)(l);

    /* ---- enter critical section (read) ---- */
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();

    if (l->readers == INT_MAX) abort();
    l->readers++;

    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
    /* ---- reading happens here (not modelled) ---- */

    /* ---- leave critical section (read) ---- */
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();

    if (l->readers == 0) abort();
    l->readers--;

    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
}

/* -------------------------------------------------------------------------------- */
/*  Writer                                                                          */
/* -------------------------------------------------------------------------------- */

void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    //@ open thread_run_data(writer)(l);

    /* Keep trying until there are no active readers. */
    for (;;)
        //@ invariant [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
    {
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();

        if (l->readers == 0) {
            //@ close rwlock_inv(l)();
            break;                               // we keep the mutex!
        }

        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
    }

    /* ---- writing happens here (not modelled) ---- */

    /* Release the lock after writing. */
    mutex_release(l->mutex);
}

/* -------------------------------------------------------------------------------- */
/*  Program entry point                                                             */
/* -------------------------------------------------------------------------------- */

// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct rwlock *l = rwlock_init();
    //@ assert l->mutex |-> ?m &*& mutex(m, rwlock_inv(l));

    /* Give half of the ownership of the mutex as well as the pointer field to
       each thread.  The first thread creation will automatically take half of
       the available fraction; the remaining half is given to the second thread. */
    //@ close thread_run_data(reader)(l);
    thread_start(reader, l);

    //@ close thread_run_data(writer)(l);
    thread_start(writer, l);

    /* Nothing left to do for main; any remaining chunks are owned by the
       spawned threads. */
    return 0;
}