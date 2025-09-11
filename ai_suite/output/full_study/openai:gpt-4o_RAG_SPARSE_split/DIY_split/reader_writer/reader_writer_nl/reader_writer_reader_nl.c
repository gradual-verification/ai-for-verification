#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    l->mutex |-> ?mutex &*&
    mutex(mutex, reader_inv(l));

predicate_ctor reader_inv(struct rwlock *l)() =
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
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    //@ open thread_run_data(reader)(l);
    mutex_acquire(l->mutex);
    //@ open reader_inv(l)();

    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    //@ close reader_inv(l)();
    mutex_release(l->mutex);

    // critical section (reading)

    mutex_acquire(l->mutex);
    //@ open reader_inv(l)();
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    //@ close reader_inv(l)();
    mutex_release(l->mutex);
    //@ leak l->mutex |-> _ &*& mutex(_, reader_inv(l));
}