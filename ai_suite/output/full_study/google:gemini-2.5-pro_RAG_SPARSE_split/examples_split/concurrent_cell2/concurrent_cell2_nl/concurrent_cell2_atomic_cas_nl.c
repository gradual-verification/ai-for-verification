#include "prelude.h"

/*@

// To model the atomic integer, we use an atomic space.
// The invariant of the atomic space holds the integer chunk.
// The 'c' parameter is the address of the integer. It is used to distinguish
// different atomic spaces for different integers.
predicate_ctor cas_inv(int* c)() = exists(?v) &*& integer(c, v);

// A handle to the atomic space. This predicate is sharable among threads
// and represents the permission to perform atomic operations on the integer at 'c'.
// The description "It requires that the cas operation is allowed on the cell"
// is captured by requiring this predicate.
predicate casable(int* c) = atomic_space_handle(cas_inv(c));

// A ghost operation that is performed atomically with the CAS.
// This is a standard VeriFast pattern that allows a client of an atomic data structure
// to update its own ghost state based on the result of the physical operation.
// This is necessary because the client cannot directly access the value of the
// integer, as it is hidden inside the atomic space.
//
// - c: the pointer to the cell
// - old_guess: the expected old value passed to atomic_cas
// - new_val: the new value passed to atomic_cas
// - read_val: the actual value read from the cell (which is the return value of atomic_cas)
typedef lemma void cas_ghost_op(int* c, int old_guess, int new_val, int read_val)();
    requires
        // The client provides its ghost state required for the operation.
        cas_op_pre(this)(c, old_guess, new_val) &*&
        // The physical state of the cell before the operation.
        integer(c, read_val);
    ensures
        // The client's updated ghost state after the operation.
        cas_op_post(this)(c, old_guess, new_val, read_val) &*&
        // The physical state of the cell after the operation.
        integer(c, read_val == old_guess ? new_val : read_val);

// Predicate families for the pre- and post-conditions of the ghost operation.
// The client of atomic_cas will define instances of these families.
predicate_family cas_op_pre(void* op)(int* c, int old_guess, int new_val);
predicate_family cas_op_post(void* op)(int* c, int old_guess, int new_val, int read_val);

@*/

// TODO: make this function pass the verification
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
    // The caller must hold a handle to the atomic integer.
    casable(c) &*&
    // The caller must provide a ghost operation that specifies how its
    // abstract state changes. This is how clients can reason about the
    // value change.
    is_cas_ghost_op(?op) &*& cas_op_pre(op)(c, old, new);
ensures
    // The handle is preserved.
    casable(c) &*&
    // The ghost operation has been performed. The client can now use its
    // postcondition to reason about the new state. The 'result' of the
    // function is the value that was read from the cell, and it is passed
    // to the postcondition.
    cas_op_post(op)(c, old, new, result);
@*/