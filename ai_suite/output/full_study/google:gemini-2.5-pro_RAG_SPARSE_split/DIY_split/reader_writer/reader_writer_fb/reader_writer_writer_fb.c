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
    // The pointer to the mutex is constant after initialization and can be shared immutably.
    // Using a dummy fraction `[_]` allows all threads to read this pointer.
    // The original `[1/2]` fraction would prevent reading the pointer,
    // making it impossible to call `mutex_acquire(l->mutex)`.
    [_]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

// TODO: make this function pass the verification
void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l);
    //@ ensures true;
{
    //@ open thread_run_data(writer)(l);
    for (;;)
        //@ invariant [_]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
    {
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
    }

    // critical section (writing)

    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
}