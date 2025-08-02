#include "stdlib.h"
#include "threading.h"

struct philosopher {
    struct lock *fork1;
    struct lock *fork2;
};

/*@

predicate_family_instance thread_run_data(philosopher_run)(struct philosopher *data) =
    data->fork1 |-> ?fork1 &*& [_]lock(fork1, ?fork1Id, _) &*&
    data->fork2 |-> ?fork2 &*& [_]lock(fork2, ?fork2Id, _) &*&
    malloc_block_philosopher(data) &*&
    lock_below(fork1Id, fork2Id) == true;

@*/


void philosopher_run(void *data) //@ : thread_run
    //@ requires thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
    //@ ensures false;
{
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    while (true)
        //@ invariant thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
    {
        // Acquire locks in the correct order: fork1 first, then fork2
        lock_acquire(fork1);
        //@ assert locked(fork1, ?fork1Id, _, currentThread, _);
        //@ assert lockset(currentThread, cons(fork1Id, nil));
        lock_acquire(fork2);
        //@ assert locked(fork2, ?fork2Id, _, currentThread, _);
        //@ assert lockset(currentThread, cons(fork2Id, cons(fork1Id, nil)));
        
        // Eat...
        
        // Release locks in reverse order
        lock_release(fork2);
        //@ assert lockset(currentThread, cons(fork1Id, nil));
        lock_release(fork1);
        //@ assert lockset(currentThread, nil);
    }
}