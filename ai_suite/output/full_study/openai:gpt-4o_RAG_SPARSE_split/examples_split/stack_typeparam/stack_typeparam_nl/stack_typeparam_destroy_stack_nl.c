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

predicate nodes(struct node* n, destructor* destructor, list<void*> values) =
  n == 0 ? 
    values == nil 
  : 
    n->data |-> ?data &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, destructor, ?nextValues) &*& values == cons(data, nextValues);

predicate stack(struct stack* stack, list<void*> values) =
  stack->first |-> ?first &*& stack->destructor |-> ?destructor &*& stack->size |-> ?size &*&
  malloc_block_stack(stack) &*& nodes(first, destructor, values) &*& length(values) == size;

@*/

// TODO: make this function pass the verification
/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
  //@ requires stack(stack, ?values);
  //@ ensures true;
{
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while (current != 0)
    //@ invariant nodes(current, destructor, ?remainingValues);
  {
    struct node* next = current->next;
    destructor(current->data);
    //@ open nodes(current, destructor, remainingValues);
    free(current);
    current = next;
  }
  //@ open nodes(0, destructor, _);
  free(stack);
}