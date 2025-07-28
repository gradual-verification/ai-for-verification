#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@
predicate nodes(struct node* n, list<void*> vs) =
  n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?nxt &*& malloc_block_node(n) &*& nodes(nxt, ?vs2) &*& vs == cons(v, vs2);

predicate_family equals_state1(void* index)(void* x1, int v1,fixpoint(unit, int, int, bool) eq_func);
predicate_family equals_state2(void* index)(void* x1, int v1,fixpoint(unit, int, int, bool) eq_func);
@*/

/*@
predicate_ctor equals_state2_ctor(equals * index, fixpoint(unit, int, int, bool) eq_func)(void* x2, int v2) =
  equals_state2(index)(x2, v2, eq_func);
  

  
predicate is_eq_func(equals* eq, fixpoint(unit, int, int, bool) eq_func) =
  true;
  
fixpoint bool contains_eq_func(list<int> vs, int v, fixpoint(unit, int, int, bool) eq_func) {
  switch(vs) {
    case nil: return false;
    case cons(h, t): return eq_func(unit, v, h) ? true : contains_eq_func(t, v, eq_func);
  }
}

predicate foreach2<t1, t2>(list<t1> xs, list<t2> vs, predicate(t1, t2) q) = 
  switch(xs) {
    case nil: return vs == nil;
    case cons(h, t):
      return switch(vs) {
        case nil: return false;
        case cons(h2, t2): return q(h, h2) &*& foreach2(t, t2, q);
      };
  }
;

@*/

// specific to cell

struct cell {
  int val;
};

/*@
predicate_family_instance equals_state1(cell_equals)(struct cell* c1, int v, fixpoint (unit, int, int,bool) eq_func) =
  c1->val |-> v &*& malloc_block_cell(c1) &*& eq_func == cell_eq_func;
  
  predicate_family_instance equals_state2(cell_equals)(struct cell* c2, int v, fixpoint (unit, int, int,bool) eq_func) =
  c2->val |-> v &*& malloc_block_cell(c2) &*& eq_func == cell_eq_func;
  
fixpoint bool cell_eq_func(unit un, int v1, int v2) {
  switch(un) {
    case unit: return v1 == v2;
  }
}
@*/


// TODO: make this function pass the verification
struct node* add(struct node* n, void* v) 
  //@ requires nodes(n, ?vs);
  //@ ensures nodes(result, cons(v, vs));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  return nn;
}


