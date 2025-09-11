#include "stdlib.h"
#include "threading.hh"

struct philosopher {
    struct lock *fork1;
    struct lock *fork2;
};

/*@

predicate_family_instance thread_run_data(philosopher_run)(struct philosopher *data) =
    data->fork1 |-> ?fork1 &*& [_]lock(fork1, ?fork1Id, _) &*&
    data->fork2 |-> ?fork2 &*& [_]lock(fork2, ?fork2Id, _) &*&
    malloc_block_philosopher(data) &*&
    lock_below(fork1Id, fork2Id) == true;

@*/

void philosopher_run(void *data) //@ : thread_run
    //@ requires thread_run_data(philosopher_run)(data) &*& lockset(currentThread, nil);
    //@ ensures false;
{
    struct philosopher *philosopher = data;
    //@ open thread_run_data(philosopher_run)(philosopher);
    struct lock *fork1 = philosopher->fork1;
    struct lock *fork2 = philosopher->fork2;
    //@ assert [_]lock(fork1, ?fork1Id, _) &*& [_]lock(fork2, ?fork2Id, _);
    //@ assert lock_below(fork1Id, fork2Id) == true;
    while (true)
        //@ invariant lockset(currentThread, nil) &*& [_]lock(fork1, fork1Id, _) &*& [_]lock(fork2, fork2Id, _);
    {
        lock_acquire(fork2);
        lock_acquire(fork1);
        lock_release(fork2);
        lock_release(fork1);
    }
}


void create_philosopher(struct lock *fork1, struct lock *fork2)
    //@ requires [_]lock(fork1, ?fork1Id, _) &*& [_]lock(fork2, ?fork2Id, _) &*& lock_below(fork1Id, fork2Id) == true;
    //@ ensures true;
{
    struct philosopher *philosopher = malloc(sizeof(struct philosopher));
    if (philosopher == 0) abort();
    philosopher->fork1 = fork1;
    philosopher->fork2 = fork2;
    //@ close thread_run_data(philosopher_run)(philosopher);
    thread_start(philosopher_run, philosopher);
}

/*@
// The lock invariant. Since the locks do not protect any data, the invariant is simply true.
predicate empty_inv() = true;
@*/

// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    // To prevent deadlock, we establish a total order on the forks (locks).
    // We will establish the order: forkA < forkB < forkC.
    // We do this by creating the locks in reverse order of their desired IDs,
    // using the lock ordering constraints of create_lock.

    // Create forkC, the "largest" lock. No constraints needed.
    //@ close create_lock_ghost_args(empty_inv, nil, nil);
    //@ close empty_inv();
    struct lock *forkC = create_lock();
    //@ open empty_inv(); // create_lock consumes the invariant
    //@ assert lock(forkC, ?forkCId, empty_inv);

    // Create forkB, such that forkB < forkC.
    // We provide forkCId as an upper bound for forkBId.
    //@ close create_lock_ghost_args(empty_inv, nil, cons(forkCId, nil));
    //@ close empty_inv();
    struct lock *forkB = create_lock();
    //@ open empty_inv();
    //@ assert lock(forkB, ?forkBId, empty_inv);
    //@ assert lock_below_all(forkBId, cons(forkCId, nil)) == true; // This gives lock_below(forkBId, forkCId)

    // Create forkA, such that forkA < forkB.
    // We provide forkBId as an upper bound for forkAId.
    //@ close create_lock_ghost_args(empty_inv, nil, cons(forkBId, nil));
    //@ close empty_inv();
    struct lock *forkA = create_lock();
    //@ open empty_inv();
    //@ assert lock(forkA, ?forkAId, empty_inv);
    //@ assert lock_below_all(forkAId, cons(forkBId, nil)) == true; // This gives lock_below(forkAId, forkBId)

    // Now we have the required lock ordering:
    // lock_below(forkAId, forkBId) == true
    // lock_below(forkBId, forkCId) == true
    // By transitivity, we also have lock_below(forkAId, forkCId) == true.

    // The threads will need fractional permissions to the locks.
    // We leak the full lock permissions, which turns them into dummy fractions `[_]lock(...)`.
    // These dummy fractions can be shared by all threads that need them.
    //@ leak lock(forkA, _, _) &*& lock(forkB, _, _) &*& lock(forkC, _, _);

    // Create the first philosopher with forks A and B.
    // The philosopher will acquire B then A, which requires lock_below(A, B). This holds.
    create_philosopher(forkA, forkB);

    // Create the second philosopher with forks B and C.
    // The philosopher will acquire C then B, which requires lock_below(B, C). This holds.
    create_philosopher(forkB, forkC);

    // Create the third philosopher with forks A and C.
    // The philosopher will acquire C then A, which requires lock_below(A, C).
    // We prove this by transitivity from lock_below(A, B) and lock_below(B, C).
    //@ lock_below_trans(forkAId, forkBId, forkCId);
    create_philosopher(forkA, forkC);
    
    return 0;
}