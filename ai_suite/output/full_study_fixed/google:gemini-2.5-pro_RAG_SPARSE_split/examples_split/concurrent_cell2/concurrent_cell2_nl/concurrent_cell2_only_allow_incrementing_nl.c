#include "assert.h"
//@ #include "list.gh"

/*@

// Fixpoint to get the last element of a list.
fixpoint t last<t>(list<t> xs) {
    switch(xs) {
        case nil: return default_value<t>;
        case cons(h, t): return t == nil ? h : last(t);
    }
}

// Fixpoint to check if one list is a prefix of another.
fixpoint bool is_prefix_of<t>(list<t> xs, list<t> ys) {
    return length(xs) <= length(ys) && take(length(xs), ys) == xs;
}

// Fixpoint to check if a list of integers is non-decreasing.
fixpoint bool is_non_decreasing(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(h, t):
            switch (t) {
                case nil: return true;
                case cons(h2, t2): return h <= h2 && is_non_decreasing(t);
            }
    }
}

// Lemma: The suffix of a non-decreasing list is also non-decreasing.
lemma void is_non_decreasing_drop(int n, list<int> xs)
    requires is_non_decreasing(xs) == true &*& 0 <= n;
    ensures is_non_decreasing(drop(n, xs)) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (n > 0) {
                is_non_decreasing_drop(n - 1, t);
            }
    }
}

// Lemma: For a non-decreasing list, the head is less than or equal to the last element.
lemma void is_non_decreasing_head_last(list<int> xs)
    requires xs != nil &*& is_non_decreasing(xs) == true;
    ensures head(xs) <= last(xs);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (t != nil) {
                is_non_decreasing_head_last(t);
            }
    }
}

// Lemma: The last element of an appended list is the last element of the second list.
lemma void last_append<t>(list<t> xs, list<t> ys)
    requires ys != nil;
    ensures last(append(xs, ys)) == last(ys);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            last_append(t, ys);
    }
}

// Lemma: For a non-decreasing appended list, the last element of the first part is not greater than the head of the second part.
lemma void is_non_decreasing_append_last_head(list<int> xs, list<int> ys)
    requires xs != nil &*& ys != nil &*& is_non_decreasing(append(xs, ys)) == true;
    ensures last(xs) <= head(ys);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (t == nil) {
            } else {
                is_non_decreasing_append_last_head(t, ys);
            }
    }
}

// Lemma: Transitivity of the prefix relation.
lemma void is_prefix_of_trans<t>(list<t> t1, list<t> t2, list<t> t3)
    requires is_prefix_of(t1, t2) == true &*& is_prefix_of(t2, t3) == true;
    ensures is_prefix_of(t1, t3) == true;
{
    if (length(t1) == length(t2)) {
    } else {
        is_prefix_of_trans(tail(t1), tail(t2), tail(t3));
    }
}

// An abstract predicate representing the permission to access the atomic cell.
predicate atomic_cell_permission(int* c);

// A predicate representing the state of an atomic cell that is only allowed to be incremented.
// It holds a fraction of the permission and the ghost "trace" of values.
predicate atomic_cell(int* c, list<int> trace) =
    [1/2]atomic_cell_permission(c) &*&
    trace != nil &*&
    is_non_decreasing(trace) == true;

@*/

/*atomic_load function
-param: c: pointer to the cell
-description: atomically load and return the value of the cell.

It doesn't have any implementation.

It ensures that the old trace is the prefix of current trace.
*/
int atomic_load(int* c);
//@ requires [?f]atomic_cell(c, ?t1);
//@ ensures [f]atomic_cell(c, ?t2) &*& is_prefix_of(t1, t2) == true &*& result == last(t2);


// TODO: make this function pass the verification
/*only_allow_incrementing function
-param: c: pointer to the cell
-description: check whether only incrementing operation is done on a cell. 

It uses an assert statement to show that two loads doesn't decrement the value. 
*/
void only_allow_incrementing(int* c)
//@ requires [?f]atomic_cell(c, ?t1);
//@ ensures [f]atomic_cell(c, ?t3) &*& is_prefix_of(t1, t3) == true;
{
  int x1 = atomic_load(c);
  //@ assert [f]atomic_cell(c, ?t2) &*& is_prefix_of(t1, t2) == true &*& x1 == last(t2);
  int x2 = atomic_load(c);
  //@ assert [f]atomic_cell(c, t3) &*& is_prefix_of(t2, t3) == true &*& x2 == last(t3);

  //@ append_take_drop_n(t3, length(t2));
  list<int> ext = drop(length(t2), t3);
  if (ext != nil) {
      //@ is_non_decreasing_append_last_head(t2, ext);
      //@ is_non_decreasing_drop(length(t2), t3);
      //@ is_non_decreasing_head_last(ext);
      //@ last_append(t2, ext);
  }

  assert(x1 <= x2);
  
  //@ is_prefix_of_trans(t1, t2, t3);
}