#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
// Define a predicate for the rwlock invariant
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?count &*&
    count >= 0;

// Define a predicate for the rwlock
predicate rwlock(struct rwlock *l) =
    l->mutex |-> ?m &*&
    mutex(m, rwlock_inv(l)) &*&
    malloc_block_rwlock(l);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `reader` function acquires shared access by using the reader-writer lock. 
 * It first increments the number of readers, and then decrements it after the critical section (using mutex).
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
void reader(struct rwlock *l) //@ : thread_run
//@ requires thread_run_data(reader)(l) &*& lockset(currentThread, nil);
//@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(reader)(l);
    //@ open rwlock(l);
    
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();

    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();
    
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
    
    //@ leak rwlock(l);
}

/*@
predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    rwlock(l);
@*/