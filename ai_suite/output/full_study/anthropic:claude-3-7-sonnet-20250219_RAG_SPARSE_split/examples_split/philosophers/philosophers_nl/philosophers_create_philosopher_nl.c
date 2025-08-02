#include "stdlib.h"
#include "threading.h"

/***
 * Struct: philosopher
 *
 * Description:
 * Represents a philosopher, each of whom requires access to two locks (forks).
 * Each philosopher operates independently in its own thread.
 */
struct philosopher {
    struct lock *fork1;
    struct lock *fork2;
};

/*@
predicate_family thread_run_data(philosopher_run)(void *data) =
    philosopher_data(data);

predicate philosopher_data(void *data) =
    data != 0 &*&
    ((struct philosopher *)data)->fork1 |-> ?fork1 &*&
    ((struct philosopher *)data)->fork2 |-> ?fork2 &*&
    [_]lock(fork1, ?lockId1, ?p1) &*&
    [_]lock(fork2, ?lockId2, ?p2) &*&
    malloc_block_philosopher(data) &*&
    lock_below(lockId2, lockId1) == true;
@*/

/***
 * Function: philosopher_run
 *
 * Description:
 * The function executed by each philosopher thread.
 * In an infinite loop, the philosopher attempts to acquire both forks,
 * and then releases them. This simulates repeated actions (e.g., "eating").
 *
 * Note: This implementation does not prevent deadlock, since multiple philosophers
 * may attempt to acquire overlapping forks in conflicting orders.
 *
@param data - a pointer to the philosopher struct passed at thread start.
 */
void philosopher_run(void *data)
//@ requires thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
//@ ensures false;
{
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    //@ open thread_run_data(philosopher_run)(data);
    while (true)
    //@ invariant philosopher->fork1 |-> fork1 &*& philosopher->fork2 |-> fork2 &*& [_]lock(fork1, ?lockId1, ?p1) &*& [_]lock(fork2, ?lockId2, ?p2) &*& malloc_block_philosopher(philosopher) &*& lockset(currentThread, nil) &*& lock_below(lockId2, lockId1) == true;
    {
        lock_acquire(fork2);
        //@ assert lockset(currentThread, cons(lockId2, nil));
        lock_acquire(fork1);
        //@ assert lockset(currentThread, cons(lockId1, cons(lockId2, nil)));
        lock_release(fork2);
        //@ assert lockset(currentThread, cons(lockId1, nil));
        lock_release(fork1);
        //@ assert lockset(currentThread, nil);
    }
}


// TODO: make this function pass the verification
/***
 * Function: create_philosopher
 *
 * Description:
 * Allocates and initializes a philosopher with two given forks (locks).
 * Starts a new thread in which the philosopher will run.
 *
@param fork1 - pointer to the first fork (lock) used by the philosopher.
@param fork2 - pointer to the second fork (lock) used by the philosopher.
 */
void create_philosopher(struct lock *fork1, struct lock *fork2)
//@ requires [_]lock(fork1, ?lockId1, ?p1) &*& [_]lock(fork2, ?lockId2, ?p2) &*& lock_below(lockId2, lockId1) == true;
//@ ensures true;
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    //@ close philosopher_data(philosopher);
    //@ close thread_run_data(philosopher_run)(philosopher);
    thread_start(philosopher_run, philosopher);
}