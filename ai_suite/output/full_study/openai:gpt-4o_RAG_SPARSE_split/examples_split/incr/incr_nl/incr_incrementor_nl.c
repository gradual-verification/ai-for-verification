#include "stdlib.h"
#include "threading.h"

/***
 * Struct: counter
 *
 * Description:
 * Represents a shared counter protected by a mutex to ensure thread-safe access.
 *
 * Fields:
 * - mutex: A pointer to a mutex that guards access to the counter.
 * - count: An integer value representing the counter.
 */
struct counter {
    struct mutex *mutex;
    int count;
};

//@ predicate_ctor counter(struct counter *counter)() = counter->count |-> ?count;

/***
 * Function: incrementor
 *
 * Description:
 * A thread function that loops infinitely, incrementing the shared counter.
 * It acquires the mutex before accessing the counter. 
 * The verification invariant guarantees safe concurrent access (i.e., the count in the counter doesn't decrease).
 *
 * @param counter - A pointer to a shared counter object.
 */
//@ predicate_family_instance thread_run_data(incrementor)(struct counter *counter) = [_]counter->mutex |-> ?mutex &*& [_]mutex(mutex, counter(counter));

void incrementor(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(incrementor)(counter);
    //@ ensures true;
{
    struct mutex *mutex = counter->mutex;
    for (;;)
        //@ invariant [_]mutex(mutex, counter(counter));
    {
        mutex_acquire(mutex);
        //@ open counter(counter)();
        if (counter->count == INT_MAX) abort();
        counter->count++;
        //@ close counter(counter)();
        mutex_release(mutex);
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) abort();
    counter->count = 0;
    //@ close counter(counter)();
    //@ close create_mutex_ghost_arg(counter(counter));
    struct mutex *mutex = create_mutex();
    counter->mutex = mutex;
    
    //@ close thread_run_data(incrementor)(counter);
    thread_start(incrementor, counter);
    
    for (;;)
        //@ invariant [_]mutex(mutex, counter(counter));
    {
        mutex_acquire(mutex);
        //@ open counter(counter)();
        // Do something with counter->count
        //@ close counter(counter)();
        mutex_release(mutex);
    }
}