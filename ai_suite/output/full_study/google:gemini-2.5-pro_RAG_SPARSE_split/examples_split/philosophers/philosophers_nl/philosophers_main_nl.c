#include "stdlib.h"
#include "threading.h"

/*@
// An empty predicate used as the invariant for all locks.
predicate empty_pred() = true;
@*/

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
// The predicate describing the data passed to a philosopher thread.
// It owns the philosopher struct, dummy fractions of the two locks (forks),
// and the knowledge that fork1 is "below" fork2 in the global lock order.
predicate_family_instance thread_run_data(philosopher_run)(void *data) =
    ((struct philosopher *)data)->fork1 |-> ?fork1 &*&
    ((struct philosopher *)data)->fork2 |-> ?fork2 &*&
    malloc_block_philosopher(data) &*&
    [_]lock(fork1, ?lockId1, empty_pred) &*&
    [_]lock(fork2, ?lockId2, empty_pred) &*&
    lock_below(lockId1, lockId2) == true;
@*/


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
    //@ requires [_]lock(fork1, ?lockId1, empty_pred) &*& [_]lock(fork2, ?lockId2, empty_pred) &*& lock_below(lockId1, lockId2) == true;
    //@ ensures true;
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    //@ close thread_run_data(philosopher_run)(philosopher);
    thread_start(philosopher_run, philosopher);
}


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
void philosopher_run(void *data) //@ : thread_run
    //@ requires thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(philosopher_run)(data);
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    //@ assert [_]lock(fork1, ?lockId1, empty_pred);
    //@ assert [_]lock(fork2, ?lockId2, empty_pred);
    //@ assert lock_below(lockId1, lockId2) == true;
    free(philosopher);

    while (true)
        //@ invariant lockset(currentThread, nil) &*& [_]lock(fork1, lockId1, empty_pred) &*& [_]lock(fork2, lockId2, empty_pred) &*& lock_below(lockId1, lockId2) == true;
    {
        lock_acquire(fork2);
        //@ open empty_pred();
        lock_acquire(fork1);
        //@ open empty_pred();
        lock_release(fork2);
        //@ close empty_pred();
        lock_release(fork1);
        //@ close empty_pred();
    }
}

/*@
// A custom specification for a main function with no arguments.
// The 'junk()' postcondition allows leaking resources, which is necessary
// here as the threads and locks live on after main returns.
typedef main_spec();
    requires true;
    ensures junk();
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
int main() //@ : main_spec
{
    // Create locks in an order that establishes a total ordering (A < B < C)
    // to prevent deadlock.
    
    //@ close create_lock_ghost_args(empty_pred, nil, nil);
    //@ close empty_pred();
    struct lock *forkC = create_lock();
    
    //@ close create_lock_ghost_args(empty_pred, nil, cons(lockIdC, nil));
    //@ close empty_pred();
    struct lock *forkB = create_lock();
    
    //@ close create_lock_ghost_args(empty_pred, nil, cons(lockIdB, nil));
    //@ close empty_pred();
    struct lock *forkA = create_lock();

    // Prove transitivity for the A < C relationship, which is required by the third philosopher.
    //@ lock_below_trans(lockIdA, lockIdB, lockIdC);
    
    // Philosopher 1: (forkA, forkB). Acquires B then A. Requires lock_below(A, B).
    create_philosopher(forkA, forkB);
    
    // Philosopher 2: (forkB, forkC). Acquires C then B. Requires lock_below(B, C).
    create_philosopher(forkB, forkC);
    
    // Philosopher 3: (forkA, forkC). Acquires C then A. Requires lock_below(A, C).
    create_philosopher(forkA, forkC);
    
    return 0;
}