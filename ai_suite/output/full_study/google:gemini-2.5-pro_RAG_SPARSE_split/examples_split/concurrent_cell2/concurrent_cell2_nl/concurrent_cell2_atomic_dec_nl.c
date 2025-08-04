#include "prelude.h"

/*@

fixpoint bool is_prefix<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return true;
        case cons(h, t): return ys != nil && h == head(ys) && is_prefix(t, tail(ys));
    }
}

lemma void is_prefix_append<t>(list<t> p, list<t> l, list<t> s)
    requires is_prefix(p, l) == true;
    ensures is_prefix(p, append(l, s)) == true;
{
    switch(p) {
        case nil:
        case cons(h, t):
            is_prefix_append(t, tail(l), s);
    }
}

// An operation that can be performed on the atomic integer.
inductive atomic_op = atomic_op_dec;

// The box class for the atomic integer.
// It holds a pointer to the integer `c` and a trace of operations.
box_class atomic_integer_box(int* c, list<atomic_op> trace) {
    // The invariant of the box: it owns the memory location of the integer.
    invariant integer(c, _);

    // The 'decrement' action.
    action decrement();
        // Precondition for the action: we need the current value.
        requires integer(c, ?v);
        // Postcondition: the value is decremented, and the trace is updated.
        ensures integer(c, v - 1) &*& trace == append(old_trace, {atomic_op_dec});

    handle_predicate is_atomic_integer_handle(int* c_handle, list<atomic_op> handle_trace) {
        invariant c == c_handle &*& is_prefix(handle_trace, trace) == true;

        preserved_by decrement() {
            is_prefix_append(handle_trace, old_trace, {atomic_op_dec});
        }
    }
}

@*/

// TODO: make this function pass the verification
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
requires is_atomic_integer_handle(?h, ?id, c, ?pre_trace);
ensures is_atomic_integer_handle(h, id, c, ?post_trace) &*& is_prefix(pre_trace, post_trace) == true;
@*/
{
    /*@
    consuming_box_predicate atomic_integer_box(id, c, ?box_pre_trace)
    consuming_handle_predicate is_atomic_integer_handle(h, c, pre_trace)
    perform_action decrement() {
        // The handle invariant `is_prefix(pre_trace, box_pre_trace)` holds here.
        // The action's `requires` clause is checked against the box invariant.
    }
    producing_box_predicate atomic_integer_box(id, c, ?box_post_trace)
    producing_handle_predicate is_atomic_integer_handle(h, c, box_post_trace);

    // From action's `ensures` clause: box_post_trace == append(box_pre_trace, {atomic_op_dec})
    // From handle's `invariant`: is_prefix(pre_trace, box_pre_trace) == true
    // We need to prove the `ensures` clause of this function.
    // The new handle has trace `box_post_trace`. So `post_trace` is `box_post_trace`.
    // We need to prove `is_prefix(pre_trace, box_post_trace)`.
    is_prefix_append(pre_trace, box_pre_trace, {atomic_op_dec});
    // This proves `is_prefix(pre_trace, box_post_trace)`.
    @*/
}
