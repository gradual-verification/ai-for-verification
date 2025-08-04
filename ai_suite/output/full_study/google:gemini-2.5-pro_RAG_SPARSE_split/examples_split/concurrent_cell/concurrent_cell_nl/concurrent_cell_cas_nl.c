#include "threading.h"
#include "stdlib.h"

/*@
fixpoint t last<t>(list<t> l) {
    switch (l) {
        case nil: return default_value<t>;
        case cons(h, t): return t == nil ? h : last(t);
    }
}

fixpoint bool prefix_of<t>(list<t> xs, list<t> ys) {
    return take(length(xs), ys) == xs;
}

lemma void take_append_length<t>(list<t> xs, list<t> ys)
    requires true;
    ensures take(length(xs), append(xs, ys)) == xs;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            take_append_length(t, ys);
    }
}

lemma void prefix_of_append<t>(list<t> xs, list<t> ys)
    requires true;
    ensures prefix_of(xs, append(xs, ys)) == true;
{
    take_append_length(xs, ys);
}

lemma void prefix_of_refl<t>(list<t> xs)
    requires true;
    ensures prefix_of(xs, xs) == true;
{
    take_length(xs);
}

lemma void last_append_one<t>(list<t> xs, t x)
    requires xs != nil;
    ensures last(append(xs, cons(x, nil))) == x;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (t == nil) {
            } else {
                last_append_one(t, x);
            }
    }
}

predicate cell_inv(struct cell *c; list<int> trace) =
    c->x |-> last(trace);

predicate cell_shared(struct cell *c; list<int> trace) =
    c->mutex |-> ?m &*&
    mutex(m, cell_inv(c, trace));
@*/

struct cell {
  int x;
  struct mutex* mutex;
};


// TODO: make this function pass the verification
/*cas function
-param: struct cell* c, int old, int new
-description: This compare-and-swap function checks if the current value of `x` in the given cell c is equal to `old`.
If it is, the function updates `x` to `new`. This operation is thread-safe due to the use of a mutex. 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the original value of `x` before the operation.
*/
int cas(struct cell* c, int old, int new)
    //@ requires [?f]cell_shared(c, ?trace_old) &*& trace_old != nil;
    /*@ ensures [f]cell_shared(c, ?trace_new) &*&
                result == last(trace_old) &*&
                prefix_of(trace_old, trace_new) == true &*&
                trace_new == (last(trace_old) == old ? append(trace_old, cons(new, nil)) : trace_old);
    @*/
{
  int res;
  mutex_acquire(c->mutex);
  //@ open cell_inv(c, trace_old);
  res = c->x;
  //@ assert res == last(trace_old);
  if(c->x == old) {
    c->x = new;
    //@ list<int> trace_new = append(trace_old, cons(new, nil));
    //@ last_append_one(trace_old, new);
    //@ prefix_of_append(trace_old, cons(new, nil));
    //@ close cell_inv(c, trace_new);
  } else {
    //@ list<int> trace_new = trace_old;
    //@ prefix_of_refl(trace_old);
    //@ close cell_inv(c, trace_old);
  }
  {
    
  }
  mutex_release(c->mutex);
  return res;
}