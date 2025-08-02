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
predicate philosopher(struct philosopher *philosopher, struct lock *fork1, struct lock *fork2) =
    philosopher->fork1 |-> fork1 &*& philosopher->fork2 |-> fork2 &*& malloc_block_philosopher(philosopher);
@*/

/*@
predicate_family_instance thread_run_data(philosopher_run)(void *data) =
    philosopher(data, ?fork1, ?fork2) &*&
    lock(fork1, ?id1, ?p1) &*& lock(fork2, ?id2, ?p2) &*&
    lock_below(id1, id2) == true;
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
//@ requires lock(fork1, ?id1, ?p1) &*& lock(fork2, ?id2, ?p2) &*& lock_below(id1, id2) == true;
//@ ensures true;
void create_philosopher(struct lock *fork1, struct lock *fork2)
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    //@ close philosopher(philosopher, fork1, fork2);
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
//@ requires thread_run_data(philosopher_run)(data);
//@ ensures true;
void philosopher_run(void *data)
{
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    while (true)
    //@ invariant philosopher(philosopher, fork1, fork2) &*& lock(fork1, ?id1, ?p1) &*& lock(fork2, ?id2, ?p2) &*& lock_below(id1, id2) == true;
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        lock_release(fork2);
        lock_release(fork1);
    }
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
//@ requires true;
//@ ensures true;
int main()
{
    //@ close create_lock_ghost_args(?p1, nil, nil);
    struct lock *forkA = create_lock();
    //@ close create_lock_ghost_args(?p2, cons(?idA, nil), nil);
    struct lock *forkB = create_lock();
    //@ close create_lock_ghost_args(?p3, cons(?idA, nil), cons(?idB, nil));
    struct lock *forkC = create_lock();
    create_philosopher(forkA, forkB);
    create_philosopher(forkB, forkC);
    create_philosopher(forkA, forkC);
    return 0;
}