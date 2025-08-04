#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
  //@ box id;
};

/*@

fixpoint bool is_prefix(trace pref, trace trace) {
  switch(trace) {
    case zero: return pref == zero;
    case inc(trace0): return pref == trace || is_prefix(pref, trace0);
    case dec(trace0): return pref == trace || is_prefix(pref, trace0);
    case cas_(old, new, trace0): return pref == trace || is_prefix(pref, trace0);
  }
}

box_class trace_extension(trace trace) {
  invariant true;
  
  action inc();
    requires true;
    ensures trace == inc(old_trace);
        
  action dec();
    requires true;
    ensures trace == dec(old_trace);
  
  action cas(int old, int new);
    requires true;
    ensures trace == cas_(old, new, old_trace);
  
  action read();
    requires true;
    ensures trace == old_trace;
    
  handle_predicate is_prefix_handle(trace prefix) {
        invariant is_prefix(prefix, trace) == true;
        
        preserved_by inc() {
        }
        preserved_by dec() {
        }
        preserved_by cas(old, new) {
        }
        preserved_by read() {
        }
  }
}

inductive trace = zero | inc(trace) | dec(trace) | cas_(int, int, trace);

typedef lemma void increment_only(struct cell* c, int v)();
  requires c->x |-> ?x;
  ensures c->x |-> x &*& v <= x;
@*/

/*@

predicate_ctor lock_invariant(struct cell* c, fixpoint(trace, bool) allowed)() =
  c->x |-> ?v &*& [_]c->id |-> ?id &*& malloc_block_cell(c) &*& exists(?trace) &*& trace_extension(id, trace) &*& execute_trace(trace) == v &*& allowed(trace) == true;
  
fixpoint int execute_trace(trace trace) {
  switch(trace) {
    case zero: return 0;
    case inc(trace0): return execute_trace(trace0) + 1;
    case dec(trace0): return execute_trace(trace0) - 1;
    case cas_(old, new, trace0): return execute_trace(trace0) == old ? new : execute_trace(trace0);
  }
}
  
predicate cell(struct cell* c, fixpoint(trace, bool) allowed;) =
  c->mutex |-> ?mutex &*& mutex(mutex, lock_invariant(c, allowed));
  
predicate observed(struct cell* c, trace trace) =
  [_]c->id |-> ?id &*& is_prefix_handle(?h, id, trace);
@*/

/*@
typedef lemma void inc_allowed(fixpoint(trace, bool) allowed)(trace t);
  requires allowed(t) == true;
  ensures allowed(inc(t)) == true;
@*/

/*@
typedef lemma void dec_allowed(fixpoint(trace, bool) allowed)(trace t);
  requires allowed(t) == true;
  ensures allowed(dec(t)) == true;
@*/

/*@
typedef lemma void cas_allowed(fixpoint(trace, bool) allowed, int old, int new)(trace t);
  requires allowed(t) == true;
  ensures allowed(cas_(old, new, t)) == true;
@*/

/*@
fixpoint bool incr_only(trace trace) {
  switch(trace) {
    case zero: return true;
    case inc(trace0): return incr_only(trace0);
    case dec(trace0): return false;
    case cas_(old, new, trace0): return old <= new && incr_only(trace0);
  }
}
@*/


int get(struct cell* c)
  //@ requires [?f]cell(c, ?allowed) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, allowed) &*& observed(c, ?trace) &*& allowed(trace) == true &*& execute_trace(trace) == result &*& is_prefix(trace0, trace) == true;
{
  int res;
  mutex_acquire(c->mutex);
  //@ open lock_invariant(c, allowed)();
  //@ assert [_]c->id |-> ?id &*& trace_extension(id, ?trace) &*& is_prefix_handle(?h, id, trace0);
  //@ is_prefix_handle_invariant(h);
  res = c->x;
  //@ assert res == execute_trace(trace);
  //@ assert allowed(trace) == true;
  //@ assert is_prefix(trace0, trace) == true;
  {
    /*@
    consuming_box_predicate trace_extension(id, trace)
    consuming_handle_predicate is_prefix_handle(h, trace0)
    perform_action read() {}
    producing_box_predicate trace_extension(trace)
    producing_handle_predicate is_prefix_handle(h, trace);
    @*/
  }
  //@ close observed(c, trace);
  //@ close lock_invariant(c, allowed)();
  mutex_release(c->mutex);
  return res;
}

/*@
lemma void incr_only_is_monotonic(trace t1, trace t2)
    requires is_prefix(t1, t2) == true &*& incr_only(t2) == true;
    ensures execute_trace(t1) <= execute_trace(t2);
{
    switch(t2) {
        case zero:
        case inc(t2_prev):
            if (t1 != t2) {
                incr_only_is_monotonic(t1, t2_prev);
            }
        case dec(t2_prev):
            assert false;
        case cas_(old, new, t2_prev):
            if (t1 != t2) {
                incr_only_is_monotonic(t1, t2_prev);
                if (execute_trace(t2_prev) == old) {
                } else {
                }
            }
    }
}
@*/

// TODO: make this function pass the verification
void only_allow_incrementing(struct cell* c)
  //@ requires [?f]cell(c, incr_only) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, incr_only);
{
  int x1 = get(c);
  //@ assert observed(c, ?trace1) &*& incr_only(trace1) == true &*& execute_trace(trace1) == x1 &*& is_prefix(trace0, trace1) == true;
  int x2 = get(c);
  //@ assert observed(c, ?trace2) &*& incr_only(trace2) == true &*& execute_trace(trace2) == x2 &*& is_prefix(trace1, trace2) == true;
  
  //@ incr_only_is_monotonic(trace1, trace2);
  
  assert x1 <= x2;
}