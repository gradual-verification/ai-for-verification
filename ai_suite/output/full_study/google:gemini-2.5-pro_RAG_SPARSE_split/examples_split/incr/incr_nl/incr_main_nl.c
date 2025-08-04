// An example where one thread repeatedly increments a shared counter,
// and another thread repeatedly observes it and asserts that the value increases.
// Demonstrates the use of ghost variables and fractional permissions to verify
// temporal properties in multithreaded programs.

#include "stdlib.h"
#include "threading.h"

/*@
// A ghost variable that can be shared between threads using fractional permissions.
// It holds the minimum value the counter is known to have.
predicate ghost_var(int val);
@*/

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

/*@
// The invariant for the mutex. It protects the counter's physical value
// and a fraction of the ghost variable. It ensures that the physical count
// is always at least the value of the ghost variable.
predicate_ctor counter_inv(struct counter *c)() =
    c->count |-> ?v &*&
    [1/2]ghost_var(?min_v) &*&
    v >= min_v;

// The resources required by the incrementor thread.
// It needs a fraction of the mutex protecting the counter.
predicate_family_instance thread_run_data(incrementor)(void *data) =
    let c = (struct counter *)data;
    [1/2]c->mutex |-> ?m &*&
    [1/2]mutex(m, counter_inv(c));
@*/


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
    //@ ensures false; // This thread loops forever.
{
    //@ open thread_run_data(incrementor)(counter);
    struct mutex *mutex = counter->mutex;
    for (;;)
        //@ invariant [1/2]mutex(mutex, counter_inv(counter));
    {
        mutex_acquire(mutex);
        //@ open counter_inv(counter)();
        if (counter->count == INT_MAX) abort();
        counter->count++;
        //@ close counter_inv(counter)();
        mutex_release(mutex);
    }
}


// TODO: make this function pass the verification
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
    //@ ensures false; // This function loops forever.
{
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) abort();
    counter->count = 0;
    
    //@ close ghost_var(0);
    
    //@ close [1/2]ghost_var(0);
    //@ close counter_inv(counter)();
    //@ close create_mutex_ghost_arg(counter_inv(counter));
    struct mutex *mutex = create_mutex();
    counter->mutex = mutex;
    
    //@ open mutex(mutex, _);
    //@ close [1/2]mutex(mutex, counter_inv(counter));
    //@ close thread_run_data(incrementor)(counter);
    thread_start(incrementor, counter);
    
    int oldCount = 0;
    for (;;)
        /*@
        invariant
            [1/2]mutex(mutex, counter_inv(counter)) &*&
            [1/2]ghost_var(?oc) &*&
            integer(&oldCount, oc);
        @*/
    {
        mutex_acquire(mutex);
        //@ open counter_inv(counter)();
        
        int count = counter->count;
        assert(count >= oldCount);
        oldCount = count;
        
        //@ open ghost_var(oldCount); // The two [1/2] fractions have been joined.
        //@ close ghost_var(count);   // Update the ghost variable to the new value.
        
        //@ close counter_inv(counter)(); // This consumes one [1/2] fraction.
        mutex_release(mutex);
        // The other [1/2] fraction remains for the loop invariant.
    }
}