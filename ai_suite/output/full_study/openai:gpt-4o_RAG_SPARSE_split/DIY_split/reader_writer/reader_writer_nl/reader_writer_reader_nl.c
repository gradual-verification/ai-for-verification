#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate rwlock(struct rwlock *l, predicate() inv) =
    l->mutex |-> ?mutex &*&
    l->readers |-> ?readers &*&
    mutex(mutex, inv) &*&
    inv() &*&
    readers >= 0;

predicate reader_inv(struct rwlock *l) =
    l->readers |-> ?readers &*&
    readers >= 0;

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
    //@ requires rwlock(l, reader_inv(l));
    //@ ensures rwlock(l, reader_inv(l));
{
    mutex_acquire(l->mutex);
    //@ open reader_inv(l);

    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    //@ close reader_inv(l);
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    //@ open reader_inv(l);
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    //@ close reader_inv(l);
    mutex_release(l->mutex);
}