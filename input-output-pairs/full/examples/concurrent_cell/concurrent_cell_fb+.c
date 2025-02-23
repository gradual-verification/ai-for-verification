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

lemma void is_prefix_refl(trace t)
  requires true;
  ensures is_prefix(t, t) == true;
{
  switch(t) {
    case zero:
    case inc(trace0): 
    case dec(trace0): 
    case cas_(old, new, trace0): 
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

struct cell* cell_create()
  //@ requires exists<fixpoint(trace, bool)>(?allowed) &*& allowed(zero) == true;
  //@ ensures result == 0 ? true : cell(result, allowed) &*& observed(result, zero);
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) return 0;
  c->x = 0;
  struct mutex* m = create_mutex();
  c->mutex = m;
  return c;
}

/*@
typedef lemma void inc_allowed(fixpoint(trace, bool) allowed)(trace t);
  requires allowed(t) == true;
  ensures allowed(inc(t)) == true;
@*/

void increment(struct cell* c)
  //@ requires [?f]cell(c, ?allowed) &*& is_inc_allowed(?lem, allowed) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, allowed) &*& is_inc_allowed(lem, allowed) &*& observed(c, ?trace) &*& is_prefix(trace0, trace) == true;
{
  mutex_acquire(c->mutex);
  if (c->x == INT_MAX) {
    abort();
  }
  c->x++;
  /*@
    consuming_box_predicate trace_extension(id, trace)
    consuming_handle_predicate is_prefix_handle(h, trace0)
    perform_action inc() {
  @*/
  {
  
  }
  /*@
    }
    producing_box_predicate trace_extension(inc(trace))
    producing_handle_predicate is_prefix_handle(h, inc(trace));
  @*/
  mutex_release(c->mutex);
}

/*@
typedef lemma void dec_allowed(fixpoint(trace, bool) allowed)(trace t);
  requires allowed(t) == true;
  ensures allowed(dec(t)) == true;
@*/

void decrement(struct cell* c)
  //@ requires [?f]cell(c, ?allowed) &*& is_dec_allowed(?lem, allowed) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, allowed) &*& is_dec_allowed(lem, allowed) &*& observed(c, ?trace) &*& is_prefix(trace0, trace) == true;
{
  mutex_acquire(c->mutex);
  if (c->x == INT_MIN) {
    abort();
  }
  c->x--;
  /*@
    consuming_box_predicate trace_extension(id, trace)
    consuming_handle_predicate is_prefix_handle(h, trace0)
    perform_action dec() {
  @*/
  {
    
  }
  /*@
    }
    producing_box_predicate trace_extension(dec(trace))
    producing_handle_predicate is_prefix_handle(h, dec(trace));
  @*/
  mutex_release(c->mutex);
}

/*@
typedef lemma void cas_allowed(fixpoint(trace, bool) allowed, int old, int new)(trace t);
  requires allowed(t) == true;
  ensures allowed(cas_(old, new, t)) == true;
@*/

int cas(struct cell* c, int old, int new)
  //@ requires [?f]cell(c, ?allowed) &*& is_cas_allowed(?lem, allowed, old, new) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, allowed) &*& is_cas_allowed(lem, allowed, old, new) &*& observed(c, ?trace) &*& allowed(trace) == true &*& is_prefix(trace0, trace) == true;
{
  int res;
  mutex_acquire(c->mutex);
  //@ open lock_invariant(c, allowed)();
  //@ open exists(?trace);
  res = c->x;
  if(c->x == old) {
    c->x = new;
  }
  /*@
    consuming_box_predicate trace_extension(id, trace)
    consuming_handle_predicate is_prefix_handle(h, trace0)
    perform_action cas(old, new) {
  @*/
  {
    
  }
  /*@
    }
    producing_box_predicate trace_extension(cas_(old, new, trace))
    producing_handle_predicate is_prefix_handle(h, cas_(old, new, trace));
  @*/
  mutex_release(c->mutex);
  return res;
}

int get(struct cell* c)
  //@ requires [?f]cell(c, ?allowed) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, allowed) &*& observed(c, ?trace) &*& allowed(trace) == true &*& execute_trace(trace) == result &*& is_prefix(trace0, trace) == true;
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  /*@
    consuming_box_predicate trace_extension(id, trace)
    consuming_handle_predicate is_prefix_handle(h, trace0)
    perform_action read() {
  @*/
  {
  }
  /*@
    }
    producing_box_predicate trace_extension(trace)
    producing_handle_predicate is_prefix_handle(h, trace);
  @*/
  mutex_release(c->mutex);
  return res;
}

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

/*@
lemma void prefix_smaller(trace t1, trace t2)
  requires incr_only(t1) == true &*& incr_only(t2) == true &*& is_prefix(t1, t2) == true;
  ensures execute_trace(t1) <= execute_trace(t2);
{
  switch(t2) {
    case zero:
    case inc(t0): if(t1 != t2) prefix_smaller(t1, t0);
    case dec(t0): 
    case cas_(old, new, t0): if(t1 != t2) prefix_smaller(t1, t0);
  }
}
@*/

void only_allow_incrementing(struct cell* c)
  //@ requires [?f]cell(c, incr_only) &*& observed(c, ?trace0);
  //@ ensures [f]cell(c, incr_only);
{
  int x1 = get(c);
  int x2 = get(c);
  //assert x1 <= x2;
}
