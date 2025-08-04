#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@

predicate rwlock_inv(struct rwlock *l) =
    l->readers |-> ?r &*& r >= 0;

predicate rwlock(struct rwlock *l) =
    l->mutex |-> ?m &*&
    malloc_block_rwlock(l) &*&
    mutex(m, rwlock_inv(l));

predicate_family_instance thread_run_data(writer)(void *data) =
    [_]rwlock((struct rwlock *)data);

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `writer` function acquires exclusive access by using the reader-writer lock. 
 * It waits until there are no readers before entering the critical section.
 *
 * @param l: the reader-writer lock to be used, which has the mutex and has number of readers >= 0
 * 
 */
void writer(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(writer)(l) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(writer)(l);
    for (;;)
        //@ invariant [_]rwlock(l) &*& lockset(currentThread, nil);
    {
        //@ open [_]rwlock(l);
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l);
        if (l->readers == 0) {
            break;
        }
        //@ close rwlock_inv(l);
        mutex_release(l->mutex);
        //@ close [_]rwlock(l);
    }

    // critical section (writing)

    //@ close rwlock_inv(l);
    mutex_release(l->mutex);
    //@ close [_]rwlock(l);
}