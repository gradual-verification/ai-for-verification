#include "stdlib.h"

/*
  Destructors
*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);

/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};

/*@

predicate nodes(struct node* n) =
  n == 0 ? true : n->data |-> _ &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);

predicate stack(struct stack* s) =
  s->first |-> ?first &*& nodes(first) &*&
  s->destructor |-> ?d &*&
  s->size |-> ?size &*&
  malloc_block_stack(s);

@*/

// TODO: make this function pass the verification
/* get_destructor function
-params: A stack

It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
  //@ requires stack(stack);
  //@ ensures stack(stack) &*& result == stack->destructor;
{
  //@ open stack(stack);
  destructor* d = stack->destructor;
  //@ close stack(stack);
  return d;
}