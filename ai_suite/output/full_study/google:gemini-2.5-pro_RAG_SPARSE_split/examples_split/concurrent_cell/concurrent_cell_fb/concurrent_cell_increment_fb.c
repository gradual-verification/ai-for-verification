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
  c->x |-> ?v &*& [_]c->id |-> ?id &*& exists(?trace) &*& trace_extension(id, trace) &*& execute_trace(trace) == v &*& allowed(trace) == true;
  
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


// TODO: make this function pass the verification
void increment(struct cell* c)
  //@ requires [?f]cell(c, ?allowed) &*& is_inc_allowed(?lem, allowed) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, allowed) &*& is_inc_allowed(lem, allowed) &*& observed(c, ?trace) &*& is_prefix(trace0, trace) == true;
{
  //@ open cell(c, allowed);
  mutex_acquire(c->mutex);
  //@ open lock_invariant(c, allowed)();
  //@ assert c->x |-> ?v &*& [_]c->id |-> ?id &*& exists(?t) &*& trace_extension(id, t) &*& execute_trace(t) == v &*& allowed(t) == true;
  //@ open observed(c, trace0);
  //@ assert is_prefix_handle(?h_obs, id, trace0);
  
  if (c->x == INT_MAX) {
    abort();
  }
  c->x++;
  
  {
    //@ open is_prefix_handle(h_obs, id, trace0);
    //@ assert is_prefix(trace0, t) == true;
    
    //@ handle h_box = create_handle trace_extension_handle(id);
    
    //@ consuming_box_predicate trace_extension(id, t)
    //@ consuming_handle_predicate trace_extension_handle(h_box)
    //@ perform_action inc() {}
    //@ producing_box_predicate trace_extension(inc(t))
    //@ producing_handle_predicate trace_extension_handle(h_box);
    
    //@ lem(t);
    //@ close lock_invariant(c, allowed)();
    
    //@ let trace = inc(t);
    
    // The old handle h_obs is preserved. Its invariant now states is_prefix(trace0, trace) == true.
    // This is exactly what we need for the ensures clause.
    //@ open is_prefix_handle(h_obs, id, trace0);
    //@ assert is_prefix(trace0, trace) == true;
    //@ close is_prefix_handle(h_obs, id, trace0);
    
    // We need to produce a new observed predicate.
    //@ create_handle h_new = is_prefix_handle(trace);
    //@ close observed(c, trace);
    
    // We don't need the old handle anymore.
    //@ leak is_prefix_handle(h_obs, _, _);
    //@ leak trace_extension_handle(h_box, _);
  }
  
  mutex_release(c->mutex);
  //@ close [f]cell(c, allowed);
}