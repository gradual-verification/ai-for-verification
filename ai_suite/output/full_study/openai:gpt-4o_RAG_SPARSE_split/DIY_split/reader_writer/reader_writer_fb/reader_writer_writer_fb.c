#include "stdlib.h"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0;

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

// TODO: make this function pass the verification
void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    //@ open thread_run_data(writer)(l);
    //@ assert [1/2]l->mutex |-> ?m;
    for (;;)
    //@ invariant [1/2]l->mutex |-> m &*& [1/2]mutex(m, rwlock_inv(l));
    {
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            //@ close rwlock_inv(l)();
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
    }

    // critical section (writing)

    // @ close rwlock_inv(l)();
    mutex_release(l->mutex);
    //@ leak [1/2] l->mutex |-> _ &*& [1/2]mutex(_, rwlock_inv(l));
}