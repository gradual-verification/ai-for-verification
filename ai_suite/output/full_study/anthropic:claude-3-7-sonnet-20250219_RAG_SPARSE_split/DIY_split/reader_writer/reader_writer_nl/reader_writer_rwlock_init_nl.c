#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
// Define a predicate for the rwlock that captures its state
predicate rwlock(struct rwlock *lock; predicate() p) =
    lock->mutex |-> ?m &*&
    lock->readers |-> ?readers &*&
    readers >= 0 &*&
    mutex(m, p) &*&
    malloc_block_rwlock(lock);

// Define the invariant for the mutex inside the rwlock
predicate_ctor rwlock_mutex_inv(struct rwlock *lock, predicate() p)() =
    lock->readers |-> ?readers &*&
    readers >= 0 &*&
    (readers == 0 ? p() : emp);

// Ghost argument for creating a rwlock
predicate create_rwlock_ghost_arg(predicate() p) = true;
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `rwlock_init` function creates a new reader-writer lock with no reader.
 *
 * The function ensures that the returned value is a reader-writer lock.
 */
struct rwlock *rwlock_init()
    //@ requires create_rwlock_ghost_arg(?p) &*& p();
    //@ ensures result == 0 ? emp : rwlock(result, p);
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    
    //@ close rwlock_mutex_inv(l, p)();
    //@ close create_mutex_ghost_arg(rwlock_mutex_inv(l, p));
    l->mutex = create_mutex();
    
    //@ close rwlock(l, p);
    return l;
}