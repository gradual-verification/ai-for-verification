#include "stdlib.h"
#include "threading.h"

struct philosopher {
    struct lock *fork1;
    struct lock *fork2;
};

/*@

predicate_family_instance thread_run_data(philosopher_run)(struct philosopher *data) =
    data->fork1 |-> ?fork1 &*& [_]lock(fork1, ?fork1Id, ?p1) &*&
    data->fork2 |-> ?fork2 &*& [_]lock(fork2, ?fork2Id, ?p2) &*&
    malloc_block_philosopher(data) &*&
    lock_below(fork1Id, fork2Id) == true;

@*/


// TODO: make this function pass the verification
void philosopher_run(void *data) //@ : thread_run
    //@ requires thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
    //@ ensures false;
{
    struct philosopher *philosopher = data;
    //@ open thread_run_data(philosopher_run)(data);
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    //@ assert [_]lock(fork1, ?fork1Id, ?p1);
    //@ assert [_]lock(fork2, ?fork2Id, ?p2);
    while (true)
        /*@
        invariant
            philosopher->fork1 |-> fork1 &*&
            philosopher->fork2 |-> fork2 &*&
            malloc_block_philosopher(philosopher) &*&
            lockset(currentThread, nil) &*&
            [_]lock(fork1, fork1Id, p1) &*&
            [_]lock(fork2, fork2Id, p2) &*&
            lock_below(fork1Id, fork2Id) == true;
        @*/
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        
        // The philosopher is "eating" here.
        // The lock invariants p1() and p2() are held.
        
        lock_release(fork2);
        lock_release(fork1);
    }
}