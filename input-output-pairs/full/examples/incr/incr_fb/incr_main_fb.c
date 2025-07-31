#include "stdlib.h"
#include "threading.h"

struct counter {
    struct mutex *mutex;
    int count;
    //@ int oldCount;
};

/*@

predicate_ctor lock_invariant(struct counter *counter)() =
    counter->count |-> ?c &*& [1/2]counter->oldCount |-> ?oldCount &*& oldCount <= c;

predicate_family_instance thread_run_data(incrementor)(struct counter *counter) =
    counter->mutex |-> ?mutex &*& [1/2]mutex(mutex, lock_invariant(counter));

@*/


void incrementor(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(incrementor)(counter);
    //@ ensures true;
{
    struct mutex *mutex = counter->mutex;
    for (;;)
    {
        mutex_acquire(mutex);
        if (counter->count == INT_MAX) abort();
        counter->count++;
        mutex_release(mutex);
    }
}


// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
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