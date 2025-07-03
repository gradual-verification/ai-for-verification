#include "stdlib.h"
#include "threading.h"

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

// Verified writer
void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    //@ open thread_run_data(writer)(l);
    struct mutex *m = l->mutex;

    for (;;)
        /*@ invariant
               [1/2]l->mutex |-> m &*&
               [1/2]mutex(m, rwlock_inv(l));
        @*/
    {
        mutex_acquire(m);
        //@ open rwlock_inv(l)();

        if (l->readers == 0) {
            //@ close rwlock_inv(l)();
            break;                       // keep the mutex held
        }

        //@ close rwlock_inv(l)();
        mutex_release(m);                // give other threads a chance
    }

    /* critical section: writer owns the lock and knows that
       l->readers == 0                                        */

    mutex_release(m);

    //@ close thread_run_data(writer)(l);
    //@ leak thread_run_data(writer)(l);
}