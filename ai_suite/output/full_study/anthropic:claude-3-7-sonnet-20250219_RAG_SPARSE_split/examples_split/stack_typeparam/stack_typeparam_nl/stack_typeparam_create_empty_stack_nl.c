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
// Define a predicate for the stack structure
predicate stack(struct stack* s; int size, destructor* d) =
    s->first |-> ?first &*&
    s->destructor |-> d &*&
    s->size |-> size &*&
    malloc_block_stack(s);

// Define a predicate for a node in the stack
predicate node(struct node* n; void* data, struct node* next) =
    n->data |-> data &*&
    n->next |-> next &*&
    malloc_block_node(n);

// Define a predicate for a linked list of nodes
predicate nodes(struct node* first, int count, destructor* d) =
    first == 0 ?
        count == 0
    :
        node(first, ?data, ?next) &*&
        nodes(next, count - 1, d);
@*/

// TODO: make this function pass the verification
/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
//@ requires destructor != 0;
//@ ensures stack(result, 0, destructor);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close stack(stack, 0, destructor);
  return stack;
}