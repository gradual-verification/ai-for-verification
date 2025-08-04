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

predicate philosopher_data(struct philosopher *p; int fork1_id, int fork2_id) =
    p->fork1 |-> ?fork1 &*&
    p->fork2 |-> ?fork2 &*&
    [1/2]lock(fork1, fork1_id, ?inv1) &*&
    [1/2]lock(fork2, fork2_id, ?inv2) &*&
    malloc_block_philosopher(p);

predicate_family_instance thread_run_data(philosopher_run)(void *data) =
    philosopher_data(data, ?fork1_id, ?fork2_id) &*&
    lock_below(fork1_id, fork2_id) == true;

@*/


// TODO: make this function pass the verification
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
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(philosopher_run)(data);
    //@ open philosopher_data(data, ?fork1_id, ?fork2_id);
    struct philosopher *philosopher = data;
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    //@ leak philosopher->fork1 |-> _ &*& philosopher->fork2 |-> _ &*& malloc_block_philosopher(philosopher);
    while (true)
        //@ invariant [1/2]lock(fork1, fork1_id, ?inv1) &*& [1/2]lock(fork2, fork2_id, ?inv2) &*& lock_below(fork1_id, fork2_id) == true &*& lockset(currentThread, nil);
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        lock_release(fork2);
        lock_release(fork1);
    }
}