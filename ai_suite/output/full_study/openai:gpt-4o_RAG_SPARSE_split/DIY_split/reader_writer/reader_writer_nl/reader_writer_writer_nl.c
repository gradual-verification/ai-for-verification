#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

//@ predicate rwlock(struct rwlock *l; int readers) =
//@     l->mutex |-> ?mutex &*& mutex(mutex, rwlock_inv(l)) &*& l->readers |-> readers &*& readers >= 0;

//@ predicate rwlock_inv(struct rwlock *l) =
//@     l->readers |-> ?readers &*& readers >= 0;

// TODO: make this function pass the verification
/***
 * Description:
 * The `writer` function acquires exclusive access by using the reader-writer lock. 
 * It waits until there are no readers before entering the critical section.
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
//@ requires rwlock(l, 0);
//@ ensures rwlock(l, 0);
void writer(struct rwlock *l) //@ : thread_run
{
    for (;;)
    //@ invariant rwlock(l, 0);
    {
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l);
        if (l->readers == 0) {
            //@ close rwlock_inv(l);
            break;
        }
        //@ close rwlock_inv(l);
        mutex_release(l->mutex);
    }

    // critical section (writing)

    //@ open rwlock_inv(l);
    mutex_release(l->mutex);
    //@ close rwlock(l, 0);
}