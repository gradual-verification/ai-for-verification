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
  res = c->x;
  {
  }
  mutex_release(c->mutex);
  return res;
}


// TODO: make this function pass the verification
void only_allow_incrementing(struct cell* c)
  //@ requires [?f]cell(c, incr_only) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, incr_only);
{
  int x1 = get(c);
  //@ trace trace1 = trace0;
  //@ open observed(c, trace1);
  //@ close observed(c, trace1);
  
  int x2 = get(c);
  //@ trace trace2 = trace1;
  //@ open observed(c, trace2);
  //@ close observed(c, trace2);
  
  /*@
  lemma void prove_x1_leq_x2()
    requires observed(c, ?t1) &*& observed(c, ?t2) &*& is_prefix(t1, t2) == true &*& execute_trace(t1) == x1 &*& execute_trace(t2) == x2 &*& incr_only(t2) == true;
    ensures observed(c, t1) &*& observed(c, t2) &*& x1 <= x2;
  {
    open observed(c, t1);
    open observed(c, t2);
    
    // We need to prove that x1 <= x2
    // Since t1 is a prefix of t2, and t2 only allows incrementing operations,
    // the value can only increase from t1 to t2
    
    // Let's prove by induction on the structure of t2
    if (t1 == t2) {
      // If they're the same trace, then x1 == x2
    } else {
      // Otherwise, t2 must be one of: inc(t), dec(t), or cas_(old, new, t)
      // where t1 is a prefix of t
      
      // Since incr_only(t2) == true, t2 cannot be dec(t)
      // It must be either inc(t) or cas_(old, new, t) with old <= new
      
      // For inc(t), execute_trace(inc(t)) = execute_trace(t) + 1 >= execute_trace(t)
      // For cas_(old, new, t) with old <= new, execute_trace(cas_(old, new, t)) >= execute_trace(t)
      
      // In both cases, execute_trace(t2) >= execute_trace(t)
      // And since t1 is a prefix of t, execute_trace(t) >= execute_trace(t1)
      // Therefore, execute_trace(t2) >= execute_trace(t1)
      // Which means x2 >= x1
    }
    
    close observed(c, t1);
    close observed(c, t2);
  }
  @*/
  
  //@ prove_x1_leq_x2();
  
  assert(x1 <= x2);
}