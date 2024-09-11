#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};


/*@
predicate nodes(struct node* n, list<void*> vs) =
  n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?nxt &*& nodes(nxt, ?vs2) &*& vs == cons(v, vs2);

predicate_family equals_pre(void* index)(void* v1, void* v2, fixpoint(unit, void*, void*, bool) eq_func);
predicate_family equals_post(void* index)(void* v1, void* v2,  fixpoint(unit, void*, void*, bool) eq_func);
@*/

typedef bool equals(void* v1, void* v2);
  //@ requires equals_pre(this)(v1, v2, ?eq_func);
  //@ ensures equals_post(this)(v1, v2, eq_func) &*& result == eq_func(unit, v1, v2);

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
  //@ requires nodes(n, ?vs) &*& is_equals(eq) == true &*& is_eq_func(eq, ?eq_func)  &*& foreach(vs, my_pre(eq, v, eq_func)) ;
  //@ ensures nodes(n, vs) &*& is_eq_func(eq, eq_func) &*& foreach(vs, my_post(eq, v, eq_func)) &*& is_equals(eq) == true &*& result == contains_eq_func(vs, v, eq_func);
{
  if(n == 0) {
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      list_contains(n->next, v, eq); // hack: just to get my_post for the remaining elements
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      return cont;
    }
  }
}

/*@
predicate_family_instance equals_pre(my_equals)(void* v1, void* v2, fixpoint(unit, void*, void*, bool) eq_func) = eq_func == my_eq_func;
predicate_family_instance equals_post(my_equals)(void* v1, void* v2, fixpoint(unit, void*, void*, bool) eq_func) = true;

fixpoint bool my_eq_func(unit un, void* v1, void* v2) {
  switch(un) {
    case unit: return v1 == v2;
  }
}
@*/

bool my_equals(void* v1, void* v2) //@: equals
  //@ requires equals_pre(my_equals)(v1, v2, ?eq_func);
  //@ ensures equals_post(my_equals)(v1, v2, eq_func) &*& result == eq_func(unit, v1, v2);
{
  if(v1 == v2) {
    return true;
  } else {
    return false;
  }
  
}

void test_contains() 
  //@ requires true;
  //@ ensures true;
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);
  bool cont = list_contains(n, (void*) 2, my_equals);
  assert(cont == true);
}

void test_does_not_contain() 
  //@ requires true;
  //@ ensures true;
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);
  bool cont = list_contains(n, (void*) 4, my_equals);
  assert(cont == false);
}


