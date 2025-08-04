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
    lock_below(fork1Id, fork2Id) == true;

@*/


void create_philosopher(struct lock *fork1, struct lock *fork2)
    //@ requires [_]lock(fork1, ?fork1Id, _) &*& [_]lock(fork2, ?fork2Id, _) &*& lock_below(fork1Id, fork2Id) == true;
    //@ ensures true;
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    thread_start(philosopher_run, philosopher);
}


void philosopher_run(void *data) //@ : thread_run
    //@ requires thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
    //@ ensures false;
{
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    while (true)
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        lock_release(fork2);
        lock_release(fork1);
    }
}


// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    //@ close create_lock_ghost_args(emp, nil, nil);
    struct lock *forkA = create_lock();
    //@ leak lock(forkA, ?forkAId, _);

    //@ close create_lock_ghost_args(emp, cons(forkAId, nil), nil);
    struct lock *forkB = create_lock();
    //@ leak lock(forkB, ?forkBId, _);

    //@ close create_lock_ghost_args(emp, cons(forkBId, nil), nil);
    struct lock *forkC = create_lock();
    //@ leak lock(forkC, ?forkCId, _);

    create_philosopher(forkA, forkB);
    create_philosopher(forkB, forkC);

    //@ lock_below_trans(forkAId, forkBId, forkCId);
    create_philosopher(forkA, forkC);
    
    return 0;
}