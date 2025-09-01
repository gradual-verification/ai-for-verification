#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

/*@

fixpoint t last<t>(list<t> xs) {
    switch(xs) {
        case nil: return default_value<t>;
        case cons(h, t): return t == nil ? h : last(t);
    }
}

fixpoint bool is_sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(h, t):
            return switch (t) {
                case nil: return true;
                case cons(h2, t2): return h <= h2 && is_sorted(t);
            };
    }
}

lemma void is_sorted_append(list<int> xs, int y)
    requires is_sorted(xs) == true &*& (xs == nil || last(xs) <= y);
    ensures is_sorted(append(xs, cons(y, nil))) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (t == nil) {
            } else {
                is_sorted_append(t, y);
            }
    }
}

lemma void is_sorted_nth_le(list<int> xs, int i, int j)
    requires is_sorted(xs) == true &*& 0 <= i &*& i <= j &*& j < length(xs);
    ensures nth(i, xs) <= nth(j, xs);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (i == 0) {
                if (j > 0) {
                    is_sorted_nth_le(t, 0, j - 1);
                }
            } else {
                is_sorted_nth_le(t, i - 1, j - 1);
            }
    }
}

fixpoint bool is_prefix_of<t>(list<t> l1, list<t> l2) {
    return take(length(l1), l2) == l1;
}

lemma void is_prefix_of_refl<t>(list<t> l)
    requires true;
    ensures is_prefix_of(l, l) == true;
{
    take_length(l);
}

lemma void take_take<t>(int n1, int n2, list<t> xs)
    requires 0 <= n1 && n1 <= n2;
    ensures take(n1, take(n2, xs)) == take(n1, xs);
{
    if (n1 == 0) {
    } else {
        switch (xs) {
            case nil:
            case cons(h, t):
                if (n2 > 0) {
                    take_take(n1 - 1, n2 - 1, t);
                }
        }
    }
}

lemma void take_append_prefix<t>(list<t> xs, list<t> ys, int n)
    requires 0 <= n && n <= length(xs);
    ensures take(n, append(xs, ys)) == take(n, xs);
{
    if (n == 0) {
    } else {
        switch (xs) {
            case nil:
            case cons(h, t):
                take_append_prefix(t, ys, n - 1);
        }
    }
}

lemma void is_prefix_of_trans<t>(list<t> l1, list<t> l2, list<t> l3)
    requires is_prefix_of(l1, l2) == true &*& is_prefix_of(l2, l3) == true;
    ensures is_prefix_of(l1, l3) == true;
{
    int len1 = length(l1);
    int len2 = length(l2);
    assert take(len1, l2) == l1;
    assert take(len2, l3) == l2;
    take_take(len1, len2, l3);
    assert take(len1, take(len2, l3)) == take(len1, l3);
}

lemma void is_prefix_of_append<t>(list<t> l1, list<t> l2, list<t> l3)
    requires is_prefix_of(l1, l2) == true;
    ensures is_prefix_of(l1, append(l2, l3)) == true;
{
    int len1 = length(l1);
    assert take(len1, l2) == l1;
    assert len1 <= length(l2);
    take_append_prefix(l2, l3, len1);
}

lemma void is_prefix_of_implies_last_le(list<int> l1, list<int> l2)
    requires is_prefix_of(l1, l2) == true &*& is_sorted(l2) == true &*& l1 != nil;
    ensures last(l1) <= last(l2);
{
    if (l1 == l2) {
    } else {
        int len1 = length(l1);
        int len2 = length(l2);
        assert len1 < len2;
        assert last(l1) == nth(len1 - 1, l1);
        nth_take(len1 - 1, len1, l2);
        assert nth(len1 - 1, l1) == nth(len1 - 1, l2);
        is_sorted_nth_le(l2, len1 - 1, len2 - 1);
        assert nth(len1 - 1, l2) <= nth(len2 - 1, l2);
        assert last(l2) == nth(len2 - 1, l2);
    }
}

box_class cell_history(list<int> trace) {
    invariant is_sorted(trace) == true &*& trace != nil;
    
    action read();
        requires true;
        ensures trace == old_trace;
        
    action write(int new_val);
        requires new_val >= last(trace);
        ensures trace == append(old_trace, cons(new_val, nil));
        
    handle_predicate is_cell_handle(list<int> known_trace) {
        invariant is_prefix_of(known_trace, trace) == true &*& is_sorted(known_trace) == true &*& known_trace != nil;
        
        preserved_by read() {
            is_prefix_of_refl(old_trace);
        }
        preserved_by write(new_val) {
            is_prefix_of_append(known_trace, old_trace, cons(new_val, nil));
            is_sorted_append(old_trace, new_val);
        }
    }
}

predicate_ctor cell_inv(struct cell *c, box box_id)() =
    c->x |-> ?v &*&
    cell_history(box_id, ?trace) &*&
    last(trace) == v;
    
predicate cell(struct cell *c; list<int> known_trace) =
    exists<box>(?box_id) &*& exists<handle>(?h) &*&
    c->mutex |-> ?m &*&
    mutex(m, cell_inv(c, box_id)) &*&
    is_cell_handle(h, box_id, known_trace);

@*/

/*get function
-param: struct cell* c
-description: This get function retrieves the current value of the `x` field in the given cell structure in a thread-safe manner (using mutex). 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the value of `x`.
*/
int get(struct cell* c)
    //@ requires cell(c, ?known_trace);
    //@ ensures cell(c, ?new_trace) &*& is_prefix_of(known_trace, new_trace) == true &*& result == last(new_trace);
{
  int res;
  //@ open cell(c, known_trace);
  //@ open exists(?box_id);
  //@ open exists(?h);
  mutex_acquire(c->mutex);
  //@ open cell_inv(c, box_id)();
  res = c->x;
  {
    /*@
    consuming_box_predicate cell_history(box_id, ?current_trace)
    consuming_handle_predicate is_cell_handle(h, known_trace)
    perform_action read() {
        is_prefix_of_refl(old_trace);
    }
    producing_box_predicate cell_history(current_trace)
    producing_handle_predicate is_cell_handle(h, current_trace);
    @*/
  }
  //@ close cell_inv(c, box_id)();
  mutex_release(c->mutex);
  //@ close cell(c, current_trace);
  return res;
}


// TODO: make this function pass the verification
/*only_allow_incrementing function
-param: struct cell* c
-description: This function checks that the value of the `x` field in the given cell structure
can only be incremented, not decremented or changed in any other way.

In the source code, it uses an assert statement to check whether the value is incremented only.
*/
void only_allow_incrementing(struct cell* c)
    //@ requires cell(c, ?trace);
    //@ ensures cell(c, ?new_trace) &*& is_prefix_of(trace, new_trace) == true;
{
  int x1 = get(c);
  //@ assert cell(c, ?trace1) &*& is_prefix_of(trace, trace1) == true &*& x1 == last(trace1);
  int x2 = get(c);
  //@ assert cell(c, ?trace2) &*& is_prefix_of(trace1, trace2) == true &*& x2 == last(trace2);
  
  //@ open cell(c, trace2);
  //@ open exists<box>(?box_id);
  //@ open exists<handle>(?h);
  //@ open is_cell_handle(h, box_id, trace2);
  //@ is_prefix_of_implies_last_le(trace1, trace2);
  assert(x1 <= x2);
  //@ close is_cell_handle(h, box_id, trace2);
  //@ close cell(c, trace2);
  
  //@ is_prefix_of_trans(trace, trace1, trace2);
}