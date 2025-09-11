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
// Define a predicate for philosopher data
predicate_family thread_run_data(philosopher_run)(void *data) =
    philosopher_data(data);

// Predicate for philosopher data
predicate philosopher_data(void *data) =
    data != 0 &*&
    ((struct philosopher *)data)->fork1 |-> ?fork1 &*&
    ((struct philosopher *)data)->fork2 |-> ?fork2 &*&
    [_]lock(fork1, ?lockId1, ?p1) &*&
    [_]lock(fork2, ?lockId2, ?p2) &*&
    malloc_block_philosopher(data) &*&
    lock_below(lockId1, lockId2) == true; // Enforce a lock ordering to prevent deadlock
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
//@ ensures false; // Function never returns
{
    struct philosopher *philosopher = data;
    //@ open thread_run_data(philosopher_run)(data);
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    
    while (true)
    //@ invariant philosopher->fork1 |-> fork1 &*& philosopher->fork2 |-> fork2 &*& [_]lock(fork1, ?lockId1, ?p1) &*& [_]lock(fork2, ?lockId2, ?p2) &*& malloc_block_philosopher(philosopher) &*& lockset(currentThread, nil) &*& lock_below(lockId1, lockId2) == true;
    {
        // Always acquire locks in order of their IDs to prevent deadlock
        lock_acquire(fork1);
        //@ assert lockset(currentThread, cons(lockId1, nil));
        lock_acquire(fork2);
        //@ assert lockset(currentThread, cons(lockId2, cons(lockId1, nil)));
        
        // Simulate eating
        
        lock_release(fork2);
        //@ assert lockset(currentThread, cons(lockId1, nil));
        lock_release(fork1);
        //@ assert lockset(currentThread, nil);
    }
}

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
//@ requires [_]lock(fork1, ?lockId1, ?p1) &*& [_]lock(fork2, ?lockId2, ?p2) &*& lock_below(lockId1, lockId2) == true;
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

/*@
// Define a predicate for the empty invariant
predicate empty_inv() = true;

// Define a predicate constructor for the empty invariant
predicate_ctor empty_inv_ctor()() = empty_inv();
@*/

// TODO: make this function pass the verification
/***
 * Function: main
 *
 * Description:
 * Initializes three forks (locks) and creates three philosophers.
 * Each philosopher receives a pair of forks that may overlap with other philosophers.
 *
 * This setup demonstrates shared resource contention among threads.
 *
@return 0 on successful completion (though in this case, the threads run indefinitely).
 */
int main()
//@ requires true;
//@ ensures true;
{
    // Create the locks with a defined ordering to prevent deadlock
    //@ close create_lock_ghost_args(empty_inv_ctor(), nil, nil);
    struct lock *forkA = create_lock();
    //@ assert lock(forkA, ?lockIdA, _);
    
    //@ close create_lock_ghost_args(empty_inv_ctor(), cons(lockIdA, nil), nil);
    struct lock *forkB = create_lock();
    //@ assert lock(forkB, ?lockIdB, _);
    //@ assert lock_above_all(lockIdB, cons(lockIdA, nil)) == true;
    
    //@ close create_lock_ghost_args(empty_inv_ctor(), cons(lockIdB, cons(lockIdA, nil)), nil);
    struct lock *forkC = create_lock();
    //@ assert lock(forkC, ?lockIdC, _);
    //@ assert lock_above_all(lockIdC, cons(lockIdB, cons(lockIdA, nil))) == true;
    
    // Create philosophers with locks in the correct order
    // Each philosopher must acquire locks in order of increasing lock IDs
    create_philosopher(forkA, forkB);
    create_philosopher(forkB, forkC);
    
    // For the third philosopher, we need to ensure the locks are in the correct order
    // Since lockIdA < lockIdB < lockIdC, we need to pass forkA and forkC in the correct order
    create_philosopher(forkA, forkC);
    
    return 0;
}