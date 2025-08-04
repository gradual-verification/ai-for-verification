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
    //@ int min_count; // Ghost field to track the minimum value the counter can have.
};

/*@

// This predicate represents the shared state protected by the mutex.
// It ties the real 'count' to a ghost 'min_count', ensuring the
// actual count never drops below the observed minimum.
predicate counter_payload(struct counter *c) =
    c->count |-> ?count &*&
    c->min_count |-> ?min_count &*&
    min_count <= count;

// This predicate constructor serves as the invariant for the mutex.
// Any thread that acquires the mutex must preserve this invariant.
predicate_ctor counter_inv(struct counter *c)() =
    counter_payload(c);

// This predicate defines the resources required by the 'incrementor' thread.
// It includes a fractional permission to the mutex, allowing multiple threads
// to share it.
predicate_family_instance thread_run_data(incrementor)(struct counter *counter) =
    counter->mutex |-> ?mutex &*&
    [?f]mutex(mutex, counter_inv(counter));

@*/


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
    //@ requires thread_run_data(incrementor)(counter) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(incrementor)(counter);
    struct mutex *mutex = counter->mutex;
    for (;;)
        //@ invariant [f]mutex(mutex, counter_inv(counter)) &*& counter->mutex |-> mutex &*& lockset(currentThread, nil);
    {
        mutex_acquire(mutex);
        //@ open counter_inv(counter)();
        //@ open counter_payload(counter);
        
        if (counter->count == INT_MAX) abort();
        counter->count++;
        
        // The invariant `min_count <= count` is maintained.
        // Before the increment, we had `min_count <= old_count`.
        // After, `count == old_count + 1`, so `min_count <= old_count < count`,
        // which implies `min_count <= count`.
        
        //@ close counter_payload(counter);
        //@ close counter_inv(counter)();
        mutex_release(mutex);
    }
}