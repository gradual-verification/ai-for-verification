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

predicate nodes(struct node* node, list<void*> values) =
  node == 0 ? 
    values == nil 
  : 
    node->data |-> ?data &*& node->next |-> ?next &*& malloc_block_node(node) &*& nodes(next, ?values0) &*& values == cons(data, values0);

predicate stack(struct stack* stack, list<void*> values) =
  stack->first |-> ?first &*& stack->destructor |-> ?destructor &*& stack->size |-> ?size &*& malloc_block_stack(stack) &*& nodes(first, values) &*& length(values) == size;

@*/

// TODO: make this function pass the verification
/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
  //@ requires stack(stack, ?values);
  //@ ensures stack(stack, values) &*& result == length(values);
{
  int size = stack->size;
  return size;
}