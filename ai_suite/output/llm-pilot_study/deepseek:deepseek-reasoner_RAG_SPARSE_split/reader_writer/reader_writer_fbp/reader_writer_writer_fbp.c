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

// Verified writer function
void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    //@ open thread_run_data(writer)(l);
    struct mutex *m = l->mutex;

    for (;;)
        //@ invariant [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l));
    {
        mutex_acquire(m);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(m);
    }

    // critical section (writing) - no specification needed

    //@ close rwlock_inv(l)();
    mutex_release(m);

    // Leak remaining permissions
    //@ leak [1/2]l->mutex |-> m;
    //@ leak [1/2]mutex(m, rwlock_inv(l));
}