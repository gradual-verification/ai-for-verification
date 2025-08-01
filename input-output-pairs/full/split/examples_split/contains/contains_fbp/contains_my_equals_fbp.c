#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};


/*@
predicate nodes(struct node* n, list<void*> vs) =
  n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?nxt &*& malloc_block_node(n) &*& nodes(nxt, ?vs2) &*& vs == cons(v, vs2);

predicate_family equals_pre(void* index)(void* v1, void* v2, fixpoint(unit, void*, void*, bool) eq_func);
predicate_family equals_post(void* index)(void* v1, void* v2,  fixpoint(unit, void*, void*, bool) eq_func);
@*/

/*@
predicate_ctor my_pre(equals * index, void* v1, fixpoint(unit, void*, void*, bool) eq_func)(void* v2) =
  equals_pre(index)(v1, v2, eq_func);
  
predicate_ctor my_post(equals * index, void* v1, fixpoint(unit, void*, void*, bool) eq_func)(void* v2) =
  equals_post(index)(v1, v2, eq_func);
  
predicate is_eq_func(equals* eq, fixpoint(unit, void*, void*, bool) eq_func) =
  true;
  
fixpoint bool contains_eq_func(list<void*> vs, void* v, fixpoint(unit, void*, void*, bool) eq_func) {
  switch(vs) {
    case nil: return false;
    case cons(h, t): return eq_func(unit, v, h) ? true : contains_eq_func(t, v, eq_func);
  }
}
@*/

/*@
predicate_family_instance equals_pre(my_equals)(void* v1, void* v2, fixpoint(unit, void*, void*, bool) eq_func) = eq_func == my_eq_func;
predicate_family_instance equals_post(my_equals)(void* v1, void* v2, fixpoint(unit, void*, void*, bool) eq_func) = true;

fixpoint bool my_eq_func(unit un, void* v1, void* v2) {
  switch(un) {
    case unit: return (uintptr_t)v1 == (uintptr_t)v2;
  }
}
@*/


typedef bool equals(void* v1, void* v2);
  //@ requires equals_pre(this)(v1, v2, ?eq_func);
  //@ ensures equals_post(this)(v1, v2, eq_func) &*& result == eq_func(unit, v1, v2);


// TODO: make this function pass the verification
bool my_equals(void* v1, void* v2) //@: equals
  //@ requires equals_pre(my_equals)(v1, v2, ?eq_func);
  //@ ensures equals_post(my_equals)(v1, v2, eq_func) &*& result == eq_func(unit, v1, v2);
{
  if((uintptr_t)v1 == (uintptr_t)v2) {
    return true;
  } else {
    return false;
  }
  
}

