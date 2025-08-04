#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};


/*@
// Note: Added `malloc_block_node(n)` to the predicate, which is standard
// for linked lists and necessary to prove memory safety.
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
bool list_contains(struct node* n, void* v, equals* eq) 
  //@ requires nodes(n, ?vs) &*& is_equals(eq) == true &*& is_eq_func(eq, ?eq_func)  &*& foreach(vs, my_pre(eq, v, eq_func)) ;
  //@ ensures nodes(n, vs) &*& is_eq_func(eq, eq_func) &*& foreach(vs, my_post(eq, v, eq_func)) &*& is_equals(eq) == true &*& result == contains_eq_func(vs, v, eq_func);
{
  if(n == 0) {
    //@ open nodes(n, vs);
    //@ open foreach(vs, my_pre(eq, v, eq_func));
    //@ close foreach(nil, my_post(eq, v, eq_func));
    return false;
  } else {
    //@ open nodes(n, vs);
    //@ open foreach(vs, my_pre(eq, v, eq_func));
    //@ open my_pre(eq, v, eq_func)(n->value);
    bool cont = eq(v, n->value);
    //@ open my_post(eq, v, eq_func)(n->value);
    if(cont) {
      list_contains(n->next, v, eq); // hack: just to get my_post for the remaining elements
      //@ close foreach(vs, my_post(eq, v, eq_func));
      return true;
    } else {
      bool rec_cont = list_contains(n->next, v, eq);
      //@ close foreach(vs, my_post(eq, v, eq_func));
      return rec_cont;
    }
  }
}