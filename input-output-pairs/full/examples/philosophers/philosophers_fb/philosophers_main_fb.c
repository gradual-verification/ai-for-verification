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


// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct lock *forkA = create_lock();
    struct lock *forkB = create_lock();
    struct lock *forkC = create_lock();
    create_philosopher(forkA, forkB);
    create_philosopher(forkB, forkC);
    create_philosopher(forkA, forkC);
    return 0;
}