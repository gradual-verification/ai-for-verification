#include "prelude.h"

/*@

// A trace is a list of events, modeled as integers.
typedef list<int> trace;

// Fixpoint to check if one trace is a prefix of another.
fixpoint bool is_prefix_of(trace prefix, trace t) {
    return length(prefix) <= length(t) && take(length(prefix), t) == prefix;
}

// Ghost predicate representing the shared state of the lock.
// This predicate is meant to be stored in an atomic_space.
// - c: pointer to the lock variable.
// - held: boolean indicating if the lock is held.
// - t: the trace.
predicate lock_shared_state(int* c; bool held, trace t);

// Ghost predicate owned by the thread that holds the lock.
// It proves ownership of the lock.
// - c: pointer to the lock variable.
// - t_acq: the trace at the time of acquisition.
predicate lock_is_held_token(int* c, trace t_acq);

// Predicate for the physical state of the lock variable.
// A value of 1 means held, 0 means free.
predicate lock_physical_state(int* c, bool held) =
    held ? integer(c, 1) : integer(c, 0);

// A higher-level predicate that bundles the thread-local resources
// for a held lock. This is what a thread owner would typically hold.
predicate lock_is_held(int* c, trace t_acq) =
    lock_is_held_token(c, t_acq) &*& lock_physical_state(c, true);

@*/

/*atomic_dec function
-param: c: pointer to the cell
-description: atomically decrement the value of the cell. 

It doesn't have any implementation.

It requires that the decrement operation is allowed on the cell.
It ensures that this decrement operation must finish at the end 
(while operations of other threads can be finished concurrently during this operation),
so the old trace is the prefix of current trace.
*/
void atomic_dec(int* c)
/*@
    requires
        [?f]atomic_space(lock_shared_state(c, true, ?t_old)) &*&
        lock_is_held_token(c, t_old) &*&
        lock_physical_state(c, true);
    ensures
        [f]atomic_space(lock_shared_state(c, false, ?t_new)) &*&
        lock_physical_state(c, false) &*&
        is_prefix_of(t_old, t_new) == true;
@*/
;


// TODO: make this function pass the verification
/*release function
-param: c: pointer to the cell
-description: release the lock by decrementing the value of c

It requires that the lock of old trace is held by the current thread,
and it ensures that the lock of the new trace is not held by no thread. 
*/
void release(int* c)
/*@
    requires
        [?f]atomic_space(lock_shared_state(c, true, ?t_old)) &*&
        lock_is_held(c, t_old);
    ensures
        [f]atomic_space(lock_shared_state(c, false, ?t_new)) &*&
        lock_physical_state(c, false) &*&
        is_prefix_of(t_old, t_new) == true;
@*/
{
  //@ open lock_is_held(c, t_old);
  atomic_dec(c);
}