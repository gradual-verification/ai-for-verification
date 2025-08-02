// An example where one thread repeatedly increments a shared counter,
// and another thread repeatedly observes it and asserts that the value increases.
// Demonstrates the use of ghost variables and fractional permissions to verify
// temporal properties in multithreaded programs.

#include "stdlib.h"
#include "threading.h"

/***
 * Struct: counter

Description:
Represents a shared counter protected by a mutex to ensure thread-safe access.

Fields:
- mutex: A pointer to a mutex that guards access to the counter.
- count: An integer value representing the counter.
 */
struct counter {
    struct mutex *mutex;
    int count;
};

//@ predicate_ctor counter_inv(struct counter *counter)() = counter->count |-> ?count;

// TODO: make this function pass the verification
/***
 * Function: incrementor

Description:
A thread function that loops infinitely, incrementing the shared counter.
It acquires the mutex before accessing the counter. 
The verification invariant guarantees safe concurrent access (i.e., the count in the counter doesn't decrease).

@param counter - A pointer to a shared counter object.
 */
void incrementor(struct counter *counter) //@ : thread_run
//@ requires thread_run_data(incrementor)(counter);
//@ ensures true;
{
    //@ open thread_run_data(incrementor)(counter);
    struct mutex *mutex = counter->mutex;
    
    for (;;)
        //@ invariant [1/3]mutex(mutex, counter_inv(counter));
    {
        mutex_acquire(mutex);
        //@ open counter_inv(counter)();
        if (counter->count == INT_MAX) abort();
        counter->count++;
        //@ close counter_inv(counter)();
        mutex_release(mutex);
    }
}

/*@
predicate_family_instance thread_run_data(incrementor)(struct counter *counter) =
    counter->mutex |-> ?mutex &*& [1/3]mutex(mutex, counter_inv(counter));
@*/