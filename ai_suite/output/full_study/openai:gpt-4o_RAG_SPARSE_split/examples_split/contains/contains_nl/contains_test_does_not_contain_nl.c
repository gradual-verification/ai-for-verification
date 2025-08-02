#include "stdlib.h"
#include "stdbool.h"

struct node {
  void* value;
  struct node* next;
};

/*@

predicate nodes(struct node* n, list<void*> vs) =
  n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate list(struct node* n, list<void*> vs) = nodes(n, vs);

typedef bool equals(void* v1, void* v2);
  //@ requires true;
  //@ ensures true;

@*/

struct node* create_list() 
  //@ requires true;
  //@ ensures list(result, nil);
{
  return 0;
}

struct node* add(struct node* n, void* v) 
  //@ requires list(n, ?vs);
  //@ ensures list(result, cons(v, vs));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  //@ close nodes(nn, cons(v, vs));
  return nn;
}

bool list_contains(struct node* n, void* v, equals* eq) 
  //@ requires list(n, ?vs) &*& is_equals(eq) == true;
  //@ ensures list(n, vs) &*& result == mem(v, vs);
{
  //@ open list(n, vs);
  if(n == 0) {
    //@ close list(n, vs);
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      //@ close list(n, vs);
      return true;
    } else {
      bool result = list_contains(n->next, v, eq);
      //@ close list(n, vs);
      return result;
    }
  }
}

bool my_equals(void* v1, void* v2) //@: equals
  //@ requires true;
  //@ ensures true;
{
  return (uintptr_t)v1 == (uintptr_t)v2;
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