#include "assert.h"
//@ #include "list.gh"

/*@

// A predicate representing a thread's permission to access the monotonic integer `c`.
// It also holds the thread's local view of the trace of values.
predicate monotonic_int(int* c, list<int> trace);

// A fixpoint function to check if a list of integers is sorted non-decreasingly.
fixpoint bool is_sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(h, t): return
            switch (t) {
                case nil: return true;
                case cons(th, tt): return h <= th && is_sorted(t);
            };
    }
}

// A fixpoint function to get the last element of a list.
fixpoint int last(list<int> xs) {
    switch (xs) {
        case nil: return 0; // Should not be called on nil lists in this context.
        case cons(h, t): return t == nil ? h : last(t);
    }
}

// Lemma: In a non-empty sorted list, the head is less than or equal to the head of the tail.
lemma void is_sorted_cons(list<int> l)
    requires is_sorted(l) == true &*& l != nil &*& tail(l) != nil;
    ensures head(l) <= head(tail(l));
{
    switch(l) { case nil: case cons(h, t): }
}

// Lemma: In a non-empty sorted list, the head is less than or equal to the last element.
lemma void last_le_last_of_suffix(list<int> l)
    requires is_sorted(l) == true &*& l != nil;
    ensures head(l) <= last(l);
{
    switch(l) {
        case nil:
        case cons(h, t):
            if (t == nil) {
            } else {
                is_sorted_cons(l);
                last_le_last_of_suffix(t);
                le_trans(h, head(t), last(t));
            }
    }
}

// Lemma: If the concatenation of two non-empty lists is sorted, then both lists are sorted,
// and the last element of the first is less than or equal to the head of the second.
lemma void is_sorted_append_inv(list<int> p, list<int> s)
    requires is_sorted(append(p, s)) == true &*& p != nil &*& s != nil;
    ensures is_sorted(p) == true &*& is_sorted(s) == true &*& last(p) <= head(s);
{
    switch(p) {
        case nil:
        case cons(h, t):
            if (t == nil) {
                is_sorted_cons(append(p, s));
            } else {
                is_sorted_cons(append(p, s));
                is_sorted_append_inv(t, s);
            }
    }
}

// Lemma: If 'prefix' is a prefix of a sorted list 'l', then the last element of 'prefix'
// is less than or equal to the last element of 'l'.
lemma void last_of_prefix_le_last(list<int> prefix, list<int> l)
    requires is_prefix_of(prefix, l) == true &*& is_sorted(l) == true &*& prefix != nil;
    ensures last(prefix) <= last(l);
{
    if (prefix == l) {
    } else {
        is_prefix_of_append(prefix, l);
        assert l == append(prefix, ?suffix);
        if (suffix != nil) {
            is_sorted_append_inv(prefix, suffix);
            last_le_last_of_suffix(suffix);
            last_append(prefix, suffix);
            le_trans(last(prefix), head(suffix), last(suffix));
        }
    }
}

@*/

/*atomic_load function
-param: c: pointer to the cell
-description: atomically load and return the value of the cell.

It doesn't have any implementation.

It ensures that the old trace is the prefix of current trace.
*/
int atomic_load(int* c);
//@ requires monotonic_int(c, ?trace_old);
/*@ ensures monotonic_int(c, ?trace_new) &*&
            is_prefix_of(trace_old, trace_new) == true &*&
            is_sorted(trace_new) == true &*&
            trace_new != nil &*&
            result == last(trace_new);
@*/


// TODO: make this function pass the verification
/*only_allow_incrementing function
-param: c: pointer to the cell
-description: check whether only incrementing operation is done on a cell. 

It uses an assert statement to show that two loads doesn't decrement the value. 
*/
void only_allow_incrementing(int* c)
    //@ requires monotonic_int(c, ?trace0) &*& is_sorted(trace0) == true &*& trace0 != nil;
    //@ ensures monotonic_int(c, _);
{
  int x1 = atomic_load(c);
  //@ assert monotonic_int(c, ?trace1);
  //@ assert is_prefix_of(trace0, trace1) == true;
  //@ assert is_sorted(trace1) == true;
  //@ assert trace1 != nil;
  //@ assert x1 == last(trace1);

  int x2 = atomic_load(c);
  //@ assert monotonic_int(c, ?trace2);
  //@ assert is_prefix_of(trace1, trace2) == true;
  //@ assert is_sorted(trace2) == true;
  //@ assert trace2 != nil;
  //@ assert x2 == last(trace2);

  //@ last_of_prefix_le_last(trace1, trace2);
  assert x1 <= x2;
}