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
{
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) abort();
    counter->count = 0;
    struct mutex *mutex = create_mutex();
    counter->mutex = mutex;
    thread_start(incrementor, counter);
    
    int oldCount = 0;
    for (;;)
    {
        mutex_acquire(mutex);
        int count = counter->count;
        assert(count >= oldCount);
        oldCount = count;
        mutex_release(mutex);
    }
}