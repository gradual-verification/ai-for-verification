#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
// Define a predicate for the rwlock invariant
predicate rwlock_inv(struct rwlock *l) =
    l->mutex |-> ?m &*&
    l->readers |-> ?readers &*&
    readers >= 0;

// Define a predicate for the rwlock
predicate rwlock(struct rwlock *l) =
    malloc_block_rwlock(l) &*&
    rwlock_inv(l);
@*/

/***
 * Description:
 * The `writer` function acquires exclusive access by using the reader-writer lock. 
 * It waits until there are no readers before entering the critical section.
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
void writer(struct rwlock *l) //@ : thread_run
    //@ requires [?f]rwlock(l) &*& lockset(currentThread, nil);
    //@ ensures [f]rwlock(l) &*& lockset(currentThread, nil);
{
    for (;;)
    //@ invariant [f]rwlock(l) &*& lockset(currentThread, nil);
    {
        mutex_acquire(l->mutex);
        //@ open [f]rwlock(l);
        //@ open rwlock_inv(l);
        if (l->readers == 0) {
            break;
        }
        //@ close rwlock_inv(l);
        //@ close [f]rwlock(l);
        mutex_release(l->mutex);
    }

    // critical section (writing)

    //@ close rwlock_inv(l);
    //@ close [f]rwlock(l);
    mutex_release(l->mutex);
}