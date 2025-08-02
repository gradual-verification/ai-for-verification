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

/***
 * Function: incrementor

Description:
A thread function that loops infinitely, incrementing the shared counter.
It acquires the mutex before accessing the counter. 
The verification invariant guarantees safe concurrent access (i.e., the count in the counter doesn't decrease).

@param counter - A pointer to a shared counter object.
 */
/*@
predicate_family_instance thread_run_data(incrementor)(struct counter *counter) =
    [1/2]counter->mutex |-> ?mutex &*& [1/2]mutex(mutex, counter_inv(counter));
@*/

void incrementor(struct counter *counter) //@ : thread_run
//@ requires thread_run_data(incrementor)(counter);
//@ ensures false;
{
    //@ open thread_run_data(incrementor)(counter);
    struct mutex *mutex = counter->mutex;
    for (;;)
        //@ invariant [1/2]counter->mutex |-> mutex &*& [1/2]mutex(mutex, counter_inv(counter));
    {
        mutex_acquire(mutex);
        //@ open counter_inv(counter)();
        if (counter->count == INT_MAX) abort();
        counter->count++;
        //@ close counter_inv(counter)();
        mutex_release(mutex);
    }
}

/***
 * Function: main
 *
 * Description:
Entry point of the program. It allocates and initializes the shared counter,
starts the incrementor thread, and continuously observes the counter value,
asserting that it never decreases over time. This demonstrates temporal
correctness under concurrent execution.

Ensures:
- The counter starts at 0.
- The incrementor thread runs concurrently to modify the counter.
- The main thread observes non-decreasing counter values using a mutex.
 */
int main() //@ : main
//@ requires true;
//@ ensures false;
{
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) abort();
    counter->count = 0;
    
    //@ close counter_inv(counter)();
    //@ close create_mutex_ghost_arg(counter_inv(counter));
    struct mutex *mutex = create_mutex();
    counter->mutex = mutex;
    
    //@ close thread_run_data(incrementor)(counter);
    thread_start(incrementor, counter);
    
    int oldCount = 0;
    for (;;)
        //@ invariant counter->mutex |-> mutex &*& [1/2]mutex(mutex, counter_inv(counter));
    {
        mutex_acquire(mutex);
        //@ open counter_inv(counter)();
        int count = counter->count;
        assert(count >= oldCount);
        oldCount = count;
        //@ close counter_inv(counter)();
        mutex_release(mutex);
    }
}