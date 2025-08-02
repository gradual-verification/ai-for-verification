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
// Define a predicate for the philosopher's data
predicate_family_instance thread_run_data(philosopher_run)(void *data) =
    data != 0 &*&
    philosopher_data(data);

// Define a predicate for the philosopher's data structure
predicate philosopher_data(struct philosopher *philosopher) =
    philosopher->fork1 |-> ?fork1 &*&
    philosopher->fork2 |-> ?fork2 &*&
    [_]lock(fork1, ?lockId1, ?p1) &*&
    [_]lock(fork2, ?lockId2, ?p2) &*&
    malloc_block_philosopher(philosopher) &*&
    lockset(currentThread, nil);
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
    //@ open thread_run_data(philosopher_run)(data);
    struct philosopher *philosopher = data;
    //@ open philosopher_data(philosopher);
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    
    while (true)
    //@ invariant [_]lock(fork1, ?lockId1, ?p1) &*& [_]lock(fork2, ?lockId2, ?p2) &*& lockset(currentThread, nil);
    {
        lock_acquire(fork2);
        //@ assert lockset(currentThread, ?locks1);
        lock_acquire(fork1);
        //@ assert lockset(currentThread, ?locks2);
        lock_release(fork2);
        //@ assert lockset(currentThread, ?locks3);
        lock_release(fork1);
        //@ assert lockset(currentThread, nil);
    }
}