#include "stdlib.h"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

/*  A writer thread only needs read-only access to the rwlock structure itself
    and a (fractional) permission on the mutex that protects the readers
    counter. */
predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

/*  A writer waits until there are no more readers.  As soon as the readers
    counter reaches 0 the writer keeps the mutex, performs its critical
    section and finally releases the mutex.  The permissions that were passed
    to the thread are leaked explicitly at the end of the function, so VeriFast
    will not complain about them.                                                */
void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures  true;
{
    //@ open thread_run_data(writer)(l);
    //@ assert [1/2]l->mutex |-> ?m;

    for (;;)
        /*@
        invariant [1/2]l->mutex |-> m &*&
                  [1/2]mutex(m, rwlock_inv(l));
        @*/
    {
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();

        if (l->readers == 0) {
            /*  The writer keeps the mutex; the invariant is re-established so
                that the mutex can be released later.                           */
            //@ close rwlock_inv(l)();
            break;
        }

        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
    }

    /* critical section (writing) */

    mutex_release(l->mutex);

    /*  The thread runs forever (or would normally terminate here).  We leak
        the resources that were supplied via thread_run_data so that VeriFast
        accepts the function.                                                    */
    //@ leak [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l));
}