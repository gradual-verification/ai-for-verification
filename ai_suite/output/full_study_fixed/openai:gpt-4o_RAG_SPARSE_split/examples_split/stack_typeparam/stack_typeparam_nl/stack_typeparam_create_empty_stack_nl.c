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
predicate nodes(struct node* n, list<void*> vs) =
  n == 0 ? vs == nil :
  n->data |-> ?d &*& n->next |-> ?next &*& malloc_block_node(n) &*&
  nodes(next, ?vs0) &*& vs == cons(d, vs0);

predicate stack(struct stack* s, list<void*> vs, destructor* d) =
  s->first |-> ?first &*& s->destructor |-> d &*& s->size |-> length(vs) &*&
  malloc_block_stack(s) &*& nodes(first, vs);
@*/

// TODO: make this function pass the verification
/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
  //@ requires true;
  //@ ensures stack(result, nil, destructor);
{
  struct stack* stack = malloc(sizeof(struct stack));
  if (stack == 0) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close nodes(0, nil);
  //@ close stack(stack, nil, destructor);
  return stack;
}