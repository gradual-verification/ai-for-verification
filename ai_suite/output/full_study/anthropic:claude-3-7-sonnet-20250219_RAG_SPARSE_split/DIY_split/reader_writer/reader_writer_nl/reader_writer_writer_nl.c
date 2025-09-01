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
    l->readers |-> ?readers &*&
    readers >= 0;

// Define a predicate for the rwlock
predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    l->mutex |-> ?m &*& mutex(m, rwlock_inv(l));
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
    //@ requires [?f]thread_run_data(writer)(l) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    for (;;)
    //@ invariant [f]thread_run_data(writer)(l) &*& lockset(currentThread, nil);
    {
        //@ open [f]thread_run_data(writer)(l);
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
        //@ close [f]thread_run_data(writer)(l);
    }

    // critical section (writing)

    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
    //@ close [f]thread_run_data(writer)(l);
    //@ leak [f]thread_run_data(writer)(l);
}