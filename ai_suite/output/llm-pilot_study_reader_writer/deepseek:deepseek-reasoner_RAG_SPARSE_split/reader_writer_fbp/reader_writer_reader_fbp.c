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

void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    //@ open thread_run_data(reader)(l);
    struct mutex *m = l->mutex;
    //@ assume(m == l->mutex); // Needed for symbolic execution
    
    // Acquire mutex to enter critical section
    mutex_acquire(m);
    //@ open rwlock_inv(l)();
    
    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    
    //@ close rwlock_inv(l)();
    mutex_release(m);
    
    // Critical section (reading) occurs here
    
    // Reacquire mutex to exit critical section
    mutex_acquire(m);
    //@ open rwlock_inv(l)();
    
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    
    //@ close rwlock_inv(l)();
    mutex_release(m);
    
    // Leak fractions since thread doesn't return them
    //@ leak [1/2]l->mutex |-> m;
    //@ leak [1/2]mutex(m, _);
}