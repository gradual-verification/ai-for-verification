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
  //@ open nodes(n, vs);
  if(n == 0) {
    //@ open foreach(nil, _);
    //@ close foreach(nil, my_post(eq, v, eq_func));
    //@ close nodes(n, vs);
    return false;
  } else {
    //@ open foreach(vs, my_pre(eq, v, eq_func));
    //@ assert vs == cons(?h, ?t);
    bool cont = eq(v, n->value);
    if(cont) {
      list_contains(n->next, v, eq); // hack: just to get my_post for the remaining elements
      //@ assert foreach(t, my_post(eq, v, eq_func));
      //@ close foreach(vs, my_post(eq, v, eq_func));
      //@ close nodes(n, vs);
      return true;
    } else {
      bool cont_rec = list_contains(n->next, v, eq);
      //@ assert foreach(t, my_post(eq, v, eq_func));
      //@ close foreach(vs, my_post(eq, v, eq_func));
      //@ close nodes(n, vs);
      return cont_rec;
    }
  }
}


bool my_equals(void* v1, void* v2) //@: equals
  //@ requires equals_pre(my_equals)(v1, v2, ?eq_func);
  //@ ensures equals_post(my_equals)(v1, v2, eq_func) &*& result == eq_func(unit, v1, v2);
{
  //@ open equals_pre(my_equals)(v1, v2, eq_func);
  if((uintptr_t)v1 == (uintptr_t)v2) {
    //@ close equals_post(my_equals)(v1, v2, eq_func);
    return true;
  } else {
    //@ close equals_post(my_equals)(v1, v2, eq_func);
    return false;
  }
}

void dispose_list(struct node* n)
  //@ requires nodes(n, _);
  //@ ensures true;
{
  struct node* current = n;
  while(current != 0)
    //@ invariant nodes(current, _);
  {
    //@ open nodes(current, _);
    struct node* next = current->next;
    free(current);
    current = next;
  }
  //@ open nodes(0, _);
}

// TODO: make this function pass the verification
void test_does_not_contain() 
  //@ requires true;
  //@ ensures true;
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);
  
  //@ list<void*> vs = cons((void*)3, cons((void*)2, cons((void*)1, nil)));
  //@ close is_eq_func(my_equals, my_eq_func);
  
  /*@
  {
    lemma void close_foreach_my_pre(list<void*> l)
        requires true;
        ensures foreach(l, my_pre(my_equals, (void*)4, my_eq_func));
    {
        switch(l) {
            case nil:
                close foreach(nil, my_pre(my_equals, (void*)4, my_eq_func));
                break;
            case cons(h, t):
                close_foreach_my_pre(t);
                // The predicate my_pre(...) expands to equals_pre(my_equals)(...) 
                // which is (my_eq_func == my_eq_func), which is true.
                close my_pre(my_equals, (void*)4, my_eq_func)(h);
                close foreach(l, my_pre(my_equals, (void*)4, my_eq_func));
                break;
        }
    }
    close_foreach_my_pre(vs);
  }
  @*/
  
  bool cont = list_contains(n, (void*) 4, my_equals);
  
  //@ assert cont == contains_eq_func(vs, (void*)4, my_eq_func);
  //@ assert cont == false;
  assert(cont == false);
  
  /*@
  {
    lemma void open_foreach_my_post(list<void*> l)
        requires foreach(l, my_post(my_equals, (void*)4, my_eq_func));
        ensures true;
    {
        open foreach(l, my_post(my_equals, (void*)4, my_eq_func));
        switch(l) {
            case nil:
                break;
            case cons(h, t):
                // The predicate my_post(...) expands to equals_post(my_equals)(...) 
                // which is true.
                open my_post(my_equals, (void*)4, my_eq_func)(h);
                open_foreach_my_post(t);
                break;
        }
    }
    open_foreach_my_post(vs);
  }
  @*/
  
  dispose_list(n);
}