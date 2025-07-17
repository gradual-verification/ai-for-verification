#include "stdlib.hh"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
// The rwlock_inv predicate defines the invariant protected by the mutex.
// It states that the 'readers' count is non-negative and includes the memory block of the lock itself.
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

// This predicate defines the resources a reader thread starts with.
// It includes a fractional permission to the mutex pointer and the mutex itself.
// This allows multiple threads to share the same lock.
predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));

@*/

// TODO: make this function pass the verification
void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    //@ open thread_run_data(reader)(l);
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();

    // Check for potential overflow before incrementing.
    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    
    // The invariant (readers >= 0) is maintained.
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();

    // A reader cannot leave if there are no readers.
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    
    // The invariant (readers >= 0) is maintained because we checked for readers > 0.
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
}