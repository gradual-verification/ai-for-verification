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
predicate philosopher(struct philosopher *p; struct lock *fork1, struct lock *fork2) =
    p->fork1 |-> fork1 &*&
    p->fork2 |-> fork2 &*&
    malloc_block_philosopher(p);

// The thread's data is a philosopher struct and fractional permissions to its two forks.
// The lock_below fact is crucial for deadlock prevention.
predicate_family_instance thread_run_data(philosopher_run)(void *data) =
    philosopher(data, ?fork1, ?fork2) &*&
    [_]lock(fork1, ?id1, emp) &*&
    [_]lock(fork2, ?id2, emp) &*&
    lock_below(id1, id2) == true;
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
    //@ ensures false; // This thread runs forever.
{
    //@ open thread_run_data(philosopher_run)(data);
    struct philosopher *philosopher = data;
    //@ open philosopher(philosopher, ?fork1, ?fork2);
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    //@ assert [_]lock(fork1, ?id1, emp);
    //@ assert [_]lock(fork2, ?id2, emp);
    //@ assert lock_below(id1, id2) == true;

    while (true)
        //@ invariant lockset(currentThread, nil) &*& [_]lock(fork1, id1, emp) &*& [_lock(fork2, id2, emp) &*& lock_below(id1, id2) == true;
    {
        // The lock_acquire contract requires lock_below(id_of_new_lock, id_of_last_acquired_lock).
        // First acquire is fine as the lockset is empty.
        lock_acquire(fork2);
        //@ open emp();
        // Second acquire requires lock_below(id1, id2), which is in our invariant.
        lock_acquire(fork1);
        //@ open emp();
        
        // Releases can happen in any order as long as the lock is held.
        lock_release(fork2);
        //@ close emp();
        lock_release(fork1);
        //@ close emp();
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
    //@ requires [_]lock(fork1, ?id1, emp) &*& [_]lock(fork2, ?id2, emp) &*& lock_below(id1, id2) == true;
    //@ ensures true;
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    //@ close philosopher(philosopher, fork1, fork2);
    //@ close thread_run_data(philosopher_run)(philosopher);
    thread_start(philosopher_run, philosopher);
}


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
    // To prevent deadlock, we establish a global lock order: A < B < C.
    // The lock_acquire contract in VeriFast enforces this ordering at compile time.

    // Create forkA. It has no lower or upper bounds.
    //@ close create_lock_ghost_args(emp, nil, nil);
    struct lock *forkA = create_lock();
    //@ open emp();
    //@ assert lock(forkA, ?idA, emp);

    // Create forkB. It must be "above" forkA.
    //@ close create_lock_ghost_args(emp, cons(idA, nil), nil);
    struct lock *forkB = create_lock();
    //@ open emp();
    //@ assert lock(forkB, ?idB, emp) &*& lock_above_all(idB, cons(idA, nil)) == true;

    // Create forkC. It must be "above" forkB.
    //@ close create_lock_ghost_args(emp, cons(idB, nil), nil);
    struct lock *forkC = create_lock();
    //@ open emp();
    //@ assert lock(forkC, ?idC, emp) &*& lock_above_all(idC, cons(idB, nil)) == true;

    // By transitivity, forkC is also "above" forkA. We need to state this explicitly.
    //@ lock_below_trans(idA, idB, idC);

    // Leak the lock resources so they can be shared by the threads.
    // This gives each thread a fractional permission to the locks.
    //@ leak lock(forkA, idA, emp);
    //@ leak lock(forkB, idB, emp);
    //@ leak lock(forkC, idC, emp);

    // Philosopher 1 uses (forkA, forkB). Acquires B then A. Needs lock_below(A, B).
    create_philosopher(forkA, forkB);
    // Philosopher 2 uses (forkB, forkC). Acquires C then B. Needs lock_below(B, C).
    create_philosopher(forkB, forkC);
    // Philosopher 3 uses (forkA, forkC). Acquires C then A. Needs lock_below(A, C).
    create_philosopher(forkA, forkC);
    
    return 0;
}