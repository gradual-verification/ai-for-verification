#include "stdlib.h"
#include "threading.h"

// A simple reader-writer lock implementation
struct rwlock {
    struct mutex *mutex;
    int readers;
};

//@ predicate_family_instance thread_run_data(writer)(struct rwlock *l) = l->mutex |-> ?mutex &*& mutex(mutex, rwlock_inv(l));

//@ predicate_ctor rwlock_inv(struct rwlock *l)() = l->readers |-> ?readers &*& readers >= 0;

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
//@requires thread_run_data(writer)(l);
//@ ensures true;
{
    for (;;)
    //@ invariant thread_run_data(writer)(l);
    {
        //@ open thread_run_data(writer)(l);
        mutex_acquire(l->mutex);
        //@ open rwlock_inv(l)();
        if (l->readers == 0) {
            //@ close rwlock_inv(l)();
            break;
        }
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
        //@ close thread_run_data(writer)(l);
    }

    // critical section (writing)

    // @ open rwlock_inv(l)();
    mutex_release(l->mutex);
    //@ close thread_run_data(writer)(l);
    //@ leak thread_run_data(writer)(l);
}