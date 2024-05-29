#include "threading.h"

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
predicate exists<t>(t x) = true;

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


/**
 * Description:
 * The cell_create function is responsible for creating and initializing a new cell structure. It allocates memory for the cell, sets its initial values, and initializes a mutex for thread-safe operations. If the memory allocation fails, it returns a null pointer.
 *

 */
struct cell* cell_create()
{
  //@ open exists(_);
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) return 0;
  c->x = 0;
  //@ close exists(zero);
  //@ create_box boxId = trace_extension(zero) and_handle h = is_prefix_handle(zero); 
  //@ c->id = boxId;
  //@ leak c->id |-> _;
  //@ close observed(c, zero);
  //@ close lock_invariant(c, allowed)();
  //@ close create_mutex_ghost_arg(lock_invariant(c, allowed));
  struct mutex* m = create_mutex();
  c->mutex = m;
  return c;
}

/*@
typedef lemma void inc_allowed(fixpoint(trace, bool) allowed)(trace t);
  requires allowed(t) == true;
  ensures allowed(inc(t)) == true;
@*/
/**
 * Description:
 * The increment function safely increments the x value of a given cell structure. 
 It uses a mutex to ensure that the operation is thread-safe, preventing concurrent modifications to the cell's x value.
 *
 * @param c A pointer to the cell structure to be incremented. The pointer must not be NULL.

 */
void increment(struct cell* c)
{
  //@ open observed(c, trace0);
  //@ assert is_prefix_handle(?h, _, trace0);
  mutex_acquire(c->mutex);
  //@ open lock_invariant(c, allowed)();
  //@ open exists(?trace);
  c->x++;
  //@ assert trace_extension(?id, trace);
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
    producing_handle_predicate is_prefix_handle(inc(trace));
  @*/
  //@ close observed(c, inc(trace));
  //@ lem(trace);
  //@ close exists(inc(trace));
  //@ close lock_invariant(c, allowed)();
  mutex_release(c->mutex);
}

/*@
typedef lemma void dec_allowed(fixpoint(trace, bool) allowed)(trace t);
  requires allowed(t) == true;
  ensures allowed(dec(t)) == true;
@*/

/**
 * Description:
 * The decrement function safely decrements the x value of a given cell structure. 
 It uses a mutex to ensure that the operation is thread-safe, preventing concurrent modifications to the cell's x value.
 *
 * @param c A pointer to the cell structure to be decremented. The pointer must not be NULL.

 */
void decrement(struct cell* c)
{
  //@ open observed(c, trace0);
  //@ assert is_prefix_handle(?h, _, trace0);
  mutex_acquire(c->mutex);
  //@ open lock_invariant(c, allowed)();
  //@ open exists(?trace);
  c->x--;
  //@ assert trace_extension(?id, trace);
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
    producing_handle_predicate is_prefix_handle(dec(trace));
  @*/
  //@ close observed(c, dec(trace));
  //@ lem(trace);
  //@ close exists(dec(trace));
  //@ close lock_invariant(c, allowed)();
  mutex_release(c->mutex);
}
/**The function is invoked with a pointer c to a cell object.
The cell object satisfies the cell predicate with a permission function allowed.
The CAS operation is allowed according to the function is_cas_allowed, which is consistent with the permission function allowed.
The cell object has been observed with the trace trace0.
.*/
/*@
typedef lemma void cas_allowed(fixpoint(trace, bool) allowed, int old, int new)(trace t);
  requires allowed(t) == true;
  ensures allowed(cas_(old, new, t)) == true;
@*/


/**
 * Description:
 * The `cas` function (compare-and-swap) checks if the current value of `x` in the given cell structure is equal to `old`. If it is, the function updates `x` to `new`. This operation is thread-safe due to the use of a mutex.
 *
 * @param c A pointer to the cell structure.
 * @param old The value to compare against the current value of `x`.
 * @param new The value to set `x` to if the current value of `x` is equal to `old`.
 * @return The original value of `x` before the operation.

 */
int cas(struct cell* c, int old, int new)
{
  //@ open observed(c, trace0);
  //@ assert is_prefix_handle(?h, _, trace0);
  int res;
  mutex_acquire(c->mutex);
  //@ open lock_invariant(c, allowed)();
  //@ open exists(?trace);
  res = c->x;
  if(c->x == old) {
    c->x = new;
  }
  //@ assert trace_extension(?id, trace);
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
    producing_handle_predicate is_prefix_handle(cas_(old, new, trace));
  @*/
  //@ close observed(c, cas_(old, new, trace));
  //@ lem(trace);
  //@ trace cs = cas_(old, new , trace);
  //@ close exists(cas_(old, new, trace));
  //@ close lock_invariant(c, allowed)();
  mutex_release(c->mutex);
  return res;
}
/**
 * Description:
 * The `get` function retrieves the current value of the `x` field in the given cell structure.
 *
 * @param c A pointer to the cell structure.
 * @return The current value of the `x` field in the cell.
 * @requires c != NULL;
 */
int get(struct cell* c)
{
  //@ open observed(c, trace0);
  //@ assert is_prefix_handle(?h, _, trace0);
  int res;
  mutex_acquire(c->mutex);
  //@ open lock_invariant(c, allowed)();
  //@ assert exists(?trace);
  res = c->x;
    //@ assert trace_extension(?id, trace);
  /*@
    consuming_box_predicate trace_extension(id, trace)
    consuming_handle_predicate is_prefix_handle(h, trace0)
    perform_action read() {
  @*/
  {
    //@ is_prefix_refl(trace);
  }
  /*@
    }
    producing_box_predicate trace_extension(trace)
    producing_handle_predicate is_prefix_handle(trace);
  @*/
  //@ close lock_invariant(c, allowed)();
  //@ close observed(c, trace);
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
/**
 * Description:
 * The `only_allow_incrementing` function ensures that the value of the `x` field in the given cell structure
 * can only be incremented, not decremented or changed in any other way.
 *
 * @param c A pointer to the cell structure.
 * @requires c != NULL;
 */
only_allow_incrementing(struct cell* c)
{
  int x1 = get(c);
  //@ assert observed(c, ?trace1);
  int x2 = get(c);
  //@ assert observed(c, ?trace2);
  //@ prefix_smaller(trace1, trace2);
  assert x1 <= x2;
  //@ leak observed(c, _);
}