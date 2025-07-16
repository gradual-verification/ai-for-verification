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

@*/

// TODO: make this function pass the verification
void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    mutex_acquire(l->mutex);

    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    mutex_release(l->mutex);
}
