#include "stdlib.h"

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

/*
  Destructors
*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);

/*@

predicate nodes(struct node* node, list<void*> values) =
    node == 0 ? 
        values == nil 
    : 
        node->data |-> ?data &*& node->next |-> ?next &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& values == cons(data, values0);

predicate stack(struct stack* stack, list<void*> values, destructor* destructor) =
    stack->first |-> ?first &*& stack->destructor |-> destructor &*& stack->size |-> length(values) &*&
    malloc_block_stack(stack) &*& nodes(first, values);

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