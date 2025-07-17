#include "stdlib.h"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

/* The reader thread  

   – Each reader first acquires the mutex and increments the
     ‘readers’ counter (making sure it does not overflow).  
   – After the critical section it acquires the mutex again and
     decrements the counter (making sure it does not become
     negative).  
   – The mutex invariant guarantees that the counter is always
     non-negative.
*/
void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures  true;
{
    //@ open thread_run_data(reader)(l);
    struct mutex *m = l->mutex;

    /* acquire and increment */
    mutex_acquire(m);
    //@ open rwlock_inv(l)();
    int n = l->readers;
    //@ produce_limits(n);

    if (n == INT_MAX) {
        //@ close rwlock_inv(l)();
        mutex_release(m);
        abort();
    }
    //@ assert n < INT_MAX;               // therefore n + 1 will not overflow
    l->readers = n + 1;
    //@ close rwlock_inv(l)();
    mutex_release(m);

    /* -------- critical section (reading) -------- */

    /* acquire and decrement */
    mutex_acquire(m);
    //@ open rwlock_inv(l)();
    n = l->readers;
    //@ produce_limits(n);

    if (n == 0) {
        //@ close rwlock_inv(l)();
        mutex_release(m);
        abort();
    }
    //@ assert n > 0;                     // therefore n - 1 is still ≥ 0
    l->readers = n - 1;
    //@ close rwlock_inv(l)();
    mutex_release(m);

    //@ close thread_run_data(reader)(l);
}