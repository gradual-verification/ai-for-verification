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

predicate nodes(struct node *node, int count) =
    node == 0 ? count == 0 : node->next |-> ?next &*& node->data |-> _ &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->first |-> ?first &*& stack->destructor |-> _ &*& stack->size |-> count &*& malloc_block_stack(stack) &*& nodes(first, count);

@*/

// TODO: make this function pass the verification
/* is_empty function
-params: A stack
This function makes sure to checks if the stack is empty and does not modify the stack. */
bool is_empty(struct stack* stack)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count) &*& result == (count == 0);
{
  //@ open stack(stack, count);
  struct node* first = stack->first;
  //@ close stack(stack, count);
  return first == 0;
}