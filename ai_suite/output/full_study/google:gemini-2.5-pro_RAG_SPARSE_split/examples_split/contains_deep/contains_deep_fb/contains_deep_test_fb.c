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


typedef bool equals(void* x1, void* x2);
  //@ requires equals_state1(this)(x1, ?v1, ?eq_func) &*& equals_state2(this)(x2, ?v2, eq_func);
  //@ ensures equals_state1(this)(x1, v1, eq_func) &*& equals_state2(this)(x2, v2, eq_func) &*& result == eq_func(unit, v1, v2);


struct node* create_list() 
  //@ requires true;
  //@ ensures nodes(result, nil);
{
  return 0;
}


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



bool list_contains(struct node* n, void* v, equals* eq) 
  //@ requires nodes(n, ?vs) &*& is_equals(eq) == true &*& is_eq_func(eq, ?eq_func) &*& equals_state1(eq)(v, ?v_val, eq_func) &*& foreach2(vs, ?vs2, equals_state2_ctor(eq, eq_func)) ;
  //@ ensures nodes(n, vs) &*& is_eq_func(eq, eq_func) &*& equals_state1(eq)(v, v_val, eq_func) &*& foreach2(vs, vs2, equals_state2_ctor(eq, eq_func)) &*& is_equals(eq) == true &*& result == contains_eq_func(vs2, v_val, eq_func);
{
  //@ open nodes(n, vs);
  if(n == 0) {
    //@ open foreach2(vs, vs2, _);
    //@ close nodes(n, vs);
    return false;
  } else {
    //@ open foreach2(vs, vs2, equals_state2_ctor(eq, eq_func));
    //@ assert n->value |-> ?v_node &*& n->next |-> ?nxt &*& nodes(nxt, ?vs_tail) &*& vs == cons(v_node, vs_tail);
    //@ assert equals_state2_ctor(eq, eq_func)(v_node, ?h2) &*& foreach2(vs_tail, ?t2, equals_state2_ctor(eq, eq_func)) &*& vs2 == cons(h2, t2);
    bool cont = eq(v, n->value);
    if(cont) {
      //@ close foreach2(vs, vs2, equals_state2_ctor(eq, eq_func));
      //@ close nodes(n, vs);
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      //@ close foreach2(vs, vs2, equals_state2_ctor(eq, eq_func));
      //@ close nodes(n, vs);
      return cont;
    }
  }
}



struct cell* create_cell(int v)
  //@ requires true;
  //@ ensures result->val |-> v &*& malloc_block_cell(result);
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) abort();
  c->val = v;
  return c;
}



bool cell_equals(struct cell* x1, struct cell* x2) //@: equals
  //@ requires equals_state1(cell_equals)(x1, ?v1, ?eq_func) &*& equals_state2(cell_equals)(x2, ?v2, eq_func);
  //@ ensures equals_state1(cell_equals)(x1, v1, eq_func) &*& equals_state2(cell_equals)(x2, v2, eq_func) &*& result == eq_func(unit, v1, v2);
{
  return x1->val == x2->val;
}


void test() 
  //@ requires true;
  //@ ensures true;
{
  struct node* n = create_list();
  struct cell* c1 = create_cell(1);
  n = add(n, c1);
  struct cell* c2 = create_cell(2);
  n = add(n, c2);
  struct cell* c3 = create_cell(3);
  n = add(n, c3);
  struct cell* c4 = create_cell(3);
  
  //@ list<void*> vs = cons(c3, cons(c2, cons(c1, nil)));
  //@ list<int> vs2 = cons(3, cons(2, cons(1, nil)));
  
  // Build the foreach2 predicate for the list elements by closing it for each element.
  //@ close foreach2(nil, nil, equals_state2_ctor(cell_equals, cell_eq_func));
  
  //@ close equals_state2_ctor(cell_equals, cell_eq_func)(c1, 1);
  //@ close foreach2(cons(c1, nil), cons(1, nil), equals_state2_ctor(cell_equals, cell_eq_func));
  
  //@ close equals_state2_ctor(cell_equals, cell_eq_func)(c2, 2);
  //@ close foreach2(cons(c2, cons(c1, nil)), cons(2, cons(1, nil)), equals_state2_ctor(cell_equals, cell_eq_func));
  
  //@ close equals_state2_ctor(cell_equals, cell_eq_func)(c3, 3);
  //@ close foreach2(vs, vs2, equals_state2_ctor(cell_equals, cell_eq_func));
  
  // Build the equals_state1 predicate for the element to find.
  //@ close equals_state1(cell_equals)(c4, 3, cell_eq_func);
  
  // The is_eq_func predicate is just 'true'.
  //@ close is_eq_func(cell_equals, cell_eq_func);
  
  bool cont = list_contains(n, c4, cell_equals);
  
  // Check the result. The list contains a cell with value 3, so cont should be true.
  //@ assert cont == true;
  
  // Clean up the predicates to avoid leaking them in the proof context.
  //@ open is_eq_func(cell_equals, cell_eq_func);
  //@ open equals_state1(cell_equals)(c4, 3, cell_eq_func);
  //@ open foreach2(vs, vs2, equals_state2_ctor(cell_equals, cell_eq_func));
  //@ open equals_state2_ctor(cell_equals, cell_eq_func)(c3, 3);
  //@ open foreach2(tail(vs), tail(vs2), equals_state2_ctor(cell_equals, cell_eq_func));
  //@ open equals_state2_ctor(cell_equals, cell_eq_func)(c2, 2);
  //@ open foreach2(tail(tail(vs)), tail(tail(vs2)), equals_state2_ctor(cell_equals, cell_eq_func));
  //@ open equals_state2_ctor(cell_equals, cell_eq_func)(c1, 1);
  //@ open foreach2(nil, nil, _);
  
  // The memory for the list and cells is leaked, but this is allowed by the contract.
  // To be fully correct, we would need to free the memory.
  struct node *current = n;
  while(current != 0)
    //@ invariant nodes(current, _);
  {
    //@ open nodes(current, _);
    struct node *next = current->next;
    free(current->value);
    free(current);
    current = next;
  }
  //@ open nodes(0, _);
  free(c4);
}