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
//@ requires exists<void*>(?p) &*& p == data;
//@ ensures true;


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

/*@
predicate node(struct node* n, void* data, struct node* next) =
  n->data |-> data &*& n->next |-> next &*& malloc_block_node(n);

predicate nodes(struct node* first, int count) =
  first == 0 ?
    count == 0
  :
    exists<void*>(?data) &*& node(first, data, ?next) &*& nodes(next, count - 1);

predicate stack(struct stack* s) =
  s->first |-> ?first &*& s->destructor |-> ?d &*& s->size |-> ?size &*&
  is_destructor(d) == true &*& nodes(first, size) &*& malloc_block_stack(s);
@*/


/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};


// TODO: make this function pass the verification
/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
//@ requires is_destructor(destructor) == true;
//@ ensures stack(result);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close nodes(0, 0);
  //@ close stack(stack);
  return stack;
}