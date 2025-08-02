#include "stdlib.h"
#include "threading.h"

struct counter {
    struct mutex *mutex;
    int count;
};

//@ predicate_ctor counter(struct counter *counter)() = 
//@     counter->count |-> ?count &*& [1/2]counter->mutex |-> ?mutex &*& [1/2]mutex(mutex, counter(counter));

void incrementor(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(incrementor)(counter);
    //@ ensures true;
{
    struct mutex *mutex = counter->mutex;
    for (;;)
    //@ invariant [1/2]mutex(mutex, counter(counter));
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
    //@ leak counter->mutex |-> mutex &*& mutex(mutex, _);
    
    //@ close thread_run_data(incrementor)(counter);
    thread_start(incrementor, counter);
    
    int oldCount = 0;
    for (;;)
    //@ invariant [1/2]mutex(mutex, counter(counter));
    {
        mutex_acquire(mutex);
        //@ open counter(counter)();
        int count = counter->count;
        assert(count >= oldCount);
        oldCount = count;
        //@ close counter(counter)();
        mutex_release(mutex);
    }
}