#include "prelude.h"

/*@
// VeriFast does not have a built-in atomic_cas function that returns the old value.
// We model it here based on the atomic operations seen in the examples.
// This requires defining the atomic_integer primitive and the lemma-based
// mechanism for specifying atomic transitions.

// An atomic integer is a location that can only be accessed through atomic operations.
// It is associated with an invariant `inv` that holds for its value.
// The `level` is used for lock-leveling to prevent deadlocks, not strictly needed here but good practice.
predicate atomic_integer(int* p, real level, predicate(int) inv);

// Predicate families for the pre- and post-conditions of the lemma for atomic_cas.
// The lemma describes the state transition of the invariant `inv`.
predicate_family_instance atomic_cas_pre(atomic_cas_lemma)(int old, int new);
predicate_family_instance atomic_cas_post(atomic_cas_lemma)(int old, int new, int old_val);

// The type of the lemma function pointer for atomic_cas.
// It takes the invariant, level, old and new values as parameters.
typedef lemma void atomic_cas_lemma(predicate(int) inv, real level, int old, int new)();
    requires
        // The lemma's precondition requires the pre-condition predicate to hold.
        atomic_cas_pre(this)(old, new) &*&
        // It also requires the atomic integer's invariant for the current value `v`.
        inv(?v) &*&
        // It requires the current box level, for lock-leveling.
        current_box_level(level);
    ensures
        // The lemma's postcondition ensures the post-condition predicate holds.
        // The post-condition is parameterized by the old value `v`.
        atomic_cas_post(this)(old, new, v) &*&
        // It ensures the invariant holds for the new value.
        inv(v == old ? new : v) &*&
        // It preserves the box level.
        current_box_level(level);

@*/

/*atomic_cas function
-param: c: pointer to the cell
-param: old: old value of the cell
-param: new: new value of the cell
-description: atomically compare the value of the cell with the old value and if it is equal to the old value, set the value of the cell to the new value. 
It returns the old value of the cell. 

It doesn't have any implementation.

It requires that the cas operation is allowed on the cell.
It ensures that this compare-and-swap operation must finish at the end 
(while operations of other threads can be finished concurrently during this operation), 
so the old trace is the prefix of current trace.
Its returns the old value of the cell.
*/
int atomic_cas(int* c, int old, int new);
/*@
    requires
        // Requires a fractional permission to the atomic integer.
        [?f]atomic_integer(c, ?level, ?inv) &*&
        // Requires a proof that `lem` is a valid lemma for this atomic_cas operation.
        is_atomic_cas_lemma(lem, inv, level, old, new) == true &*&
        // Requires the lemma's pre-condition.
        atomic_cas_pre(lem)(old, new);
    ensures
        // Returns the fractional permission to the atomic integer.
        [f]atomic_integer(c, level, inv) &*&
        // Ensures the lemma's post-condition, which depends on the `result` (the old value).
        atomic_cas_post(lem)(old, new, result);
@*/

/*@
// The invariant for the lock's atomic integer.
// If the lock's value is 0 (unlocked), it holds the protected resource `I`.
// Otherwise, the resource is held by the lock owner.
predicate_ctor lock_inv(predicate() I)(int val) = val == 0 ? I() : true;

// A lock is an atomic integer governed by the `lock_inv` predicate.
predicate lock(int* c, predicate() I) =
    atomic_integer(c, ?level, lock_inv(I));
    
// A thread that holds the lock has a fractional permission to the atomic integer
// and also owns the protected resource `I`.
predicate locked(int* c, predicate() I, real f) =
    [f]atomic_integer(c, ?level, lock_inv(I)) &*& I();
@*/

// TODO: make this function pass the verification
/*acquire function
-param: c: pointer to the cell
-description: acquire the lock by compare-and-swaping the value of c with 0 to 1. 

It ensures that in the end, the lock is acquired by the current thread.
*/
void acquire(int* c)
    //@ requires [?f]lock(c, ?I);
    //@ ensures locked(c, I, f);
{
  //@ open lock(c, I);
  while(true)
    //@ invariant [f]atomic_integer(c, ?level, lock_inv(I));
  {
    /*@
    // Define the pre- and post-condition predicates for the CAS lemma.
    predicate_family_instance atomic_cas_pre(acquire_lemma)(int old, int new) = true;
    predicate_family_instance atomic_cas_post(acquire_lemma)(int old, int new, int old_val) =
        // If the CAS succeeds (old_val was 0), the post-condition provides the protected resource `I`.
        old_val == 0 ? I() : true;
    
    // Define the lemma that describes the state transition for acquiring the lock.
    lemma void acquire_lemma()
        requires
            atomic_cas_pre(acquire_lemma)(0, 1) &*&
            lock_inv(I)(?v) &*& current_box_level(level);
        ensures
            atomic_cas_post(acquire_lemma)(0, 1, v) &*&
            lock_inv(I)(v == 0 ? 1 : v) &*& current_box_level(level);
    {
        open atomic_cas_pre(acquire_lemma)(0, 1);
        open lock_inv(I)(v);
        if (v == 0) {
            // The invariant I() is consumed from lock_inv(I)(0) and will be produced
            // in the post-condition predicate if the CAS is successful.
        }
        close lock_inv(I)(v == 0 ? 1 : v);
        close atomic_cas_post(acquire_lemma)(0, 1, v);
    }
    @*/
    //@ produce_lemma_function_pointer_chunk(acquire_lemma) : atomic_cas_lemma(lock_inv(I), level, 0, 1)() { call(); };
    //@ close atomic_cas_pre(acquire_lemma)(0, 1);
    int read = atomic_cas(c, 0, 1);
    //@ open atomic_cas_post(acquire_lemma)(0, 1, read);
    if(read == 0) {
      // The CAS was successful, the old value was 0.
      // The post-condition gives us the invariant `I()`.
      // We now have `[f]atomic_integer(...)` and `I()`, which is the `locked` predicate.
      break;
    }
  }
  //@ close locked(c, I, f);
}