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
predicate philosopher(struct philosopher *p, struct lock *fork1, struct lock *fork2) =
    p->fork1 |-> fork1 &*& p->fork2 |-> fork2 &*& malloc_block_philosopher(p);
@*/

/*@
predicate_family_instance thread_run_data(philosopher_run)(void *data) =
    philosopher(data, ?fork1, ?fork2) &*&
    lock(fork1, ?id1, ?p1) &*& lock(fork2, ?id2, ?p2) &*&
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
    //@ requires thread_run_data(philosopher_run)(data);
    //@ ensures true;
{
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    while (true)
    //@ invariant thread_run_data(philosopher_run)(data);
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        lock_release(fork2);
        lock_release(fork1);
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
    //@ requires lock(fork1, ?id1, ?p1) &*& lock(fork2, ?id2, ?p2) &*& lock_below(id1, id2) == true;
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