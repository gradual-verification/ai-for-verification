#include "stdlib.h"
#include "threading.h"

struct philosopher {
    struct lock *fork1;
    struct lock *fork2;
};

/*@

predicate_family_instance thread_run_data(philosopher_run)(struct philosopher *data) =
    data->fork1 |-> ?fork1 &*&
    data->fork2 |-> ?fork2 &*&
    malloc_block_philosopher(data) &*&
    [_]lock(fork1, ?fork1Id, _) &*&
    [_]lock(fork2, ?fork2Id, _) &*&
    lock_below(fork1Id, fork2Id) == true;

@*/


void philosopher_run(void *data) //@ : thread_run
    //@ requires thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
    //@ ensures false;
{
    //@ open thread_run_data(philosopher_run)(data);
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    while (true)
        //@ invariant [_]lock(fork1, ?fork1Id, _) &*& [_]lock(fork2, ?fork2Id, _) &*& lock_below(fork1Id, fork2Id) == true &*& lockset(currentThread, nil);
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        lock_release(fork2);
        lock_release(fork1);
    }
}


// TODO: make this function pass the verification
void create_philosopher(struct lock *fork1, struct lock *fork2)
    //@ requires [_]lock(fork1, ?fork1Id, _) &*& [_]lock(fork2, ?fork2Id, _) &*& lock_below(fork1Id, fork2Id) == true;
    //@ ensures true;
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    //@ close thread_run_data(philosopher_run)(philosopher);
    thread_start(philosopher_run, philosopher);
}