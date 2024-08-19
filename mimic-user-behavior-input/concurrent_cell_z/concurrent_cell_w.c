#include "threading.h"

struct cell {
  int x;
  struct mutex* mutex;
  //@ box id;
};



/*@
predicate exists<t>(t x) = true;

predicate_ctor lock_invariant(struct cell* c, fixpoint(trace, bool) allowed)() =
  c->x |-> ?v &*& [_]c->id |-> ?id&*& exists(?trace) &*& trace_extension(id, trace) &*& execute_trace(trace) == v &*& allowed(trace) == true;
  

predicate_ctor lock_invariant_functional(struct cell* c, fixpoint(trace, bool) allowed)() =
  c->x |-> ?v  &*& exists(?trace) &*& trace_extension(id, trace) &*& execute_trace(trace) == v &*& allowed(trace) == true;

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




void increment(struct cell* c)
 //@ requires is_inc_allowed(?lem, allowed) &*& observed(c, ?trace0);
  //@ ensures is_inc_allowed(lem, allowed) &*& observed(c, ?trace) &*& is_prefix(trace0, trace) == true;
{

  mutex_acquire(c->mutex);

  c->x++;

  {
  
  }

  mutex_release(c->mutex);
}

/*@
typedef lemma void dec_allowed(fixpoint(trace, bool) allowed)(trace t);
  requires allowed(t) == true;
  ensures allowed(dec(t)) == true;
@*/




void decrement(struct cell* c)
 //@ requires is_dec_allowed(?lem, allowed) &*& observed(c, ?trace0);
  //@ ensures is_dec_allowed(lem, allowed) &*& observed(c, ?trace) &*& is_prefix(trace0, trace) == true;
{

  mutex_acquire(c->mutex);

  c->x--;

  {
    
  }

  mutex_release(c->mutex);
}





int cas(struct cell* c, int old, int new)
 //@ requires  is_cas_allowed(?lem, allowed, old, new) &*& observed(c, ?trace0);
  //@ ensures  is_cas_allowed(lem, allowed, old, new) &*& observed(c, ?trace) &*& allowed(trace) == true &*& is_prefix(trace0, trace) == true;
{
  
  int res;
  mutex_acquire(c->mutex);
  
  res = c->x;
  if(c->x == old) {
    c->x = new;
  }

  {
    
  }

  mutex_release(c->mutex);
  return res;
}

int get(struct cell* c)
  //@ requires observed(c, ?trace0);
  //@ ensures  observed(c, ?trace) &*& allowed(trace) == true &*& execute_trace(trace) == result &*& is_prefix(trace0, trace) == true;
{
  
  int res;
  mutex_acquire(c->mutex);

  res = c->x;
 
  {
   
  }

  mutex_release(c->mutex);
  return res;
}





void only_allow_incrementing(struct cell* c)
 //@ requires c != NULL;
//@ ensures true &*& x1<=x2;
{
  int x1 = get(c);

  int x2 = get(c);

  assert x1 <= x2;

}
