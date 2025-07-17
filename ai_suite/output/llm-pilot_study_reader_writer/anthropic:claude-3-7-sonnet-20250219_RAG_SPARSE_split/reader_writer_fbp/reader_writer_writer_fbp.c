#include "stdlib.h"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    //@ open thread_run_data(writer)(l);
    struct mutex *mutex = l->mutex;
    //@ assert [1/2]mutex(mutex, rwlock_inv(l));
    
    for (;;)
    {
        mutex_acquire(mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            //@ close rwlock_inv(l)();
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(mutex);
    }

    // critical section (writing)

    //@ open rwlock_inv(l)();
    //@ close rwlock_inv(l)();
    mutex_release(mutex);
}