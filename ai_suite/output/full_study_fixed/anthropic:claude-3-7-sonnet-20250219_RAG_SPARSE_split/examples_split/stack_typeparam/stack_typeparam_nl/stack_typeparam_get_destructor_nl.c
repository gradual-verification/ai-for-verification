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
// Define predicates for the stack and nodes
predicate node(struct node* n; void* data) =
  n != 0 &*&
  n->data |-> data &*&
  n->next |-> _ &*&
  malloc_block_node(n);

predicate nodes(struct node* first, int count) =
  first == 0 ?
    count == 0
  :
    node(first, _) &*&
    first->next |-> ?next &*&
    nodes(next, count - 1);

predicate stack(struct stack* s, int size) =
  s != 0 &*&
  s->first |-> ?first &*&
  s->destructor |-> ?d &*&
  s->size |-> size &*&
  nodes(first, size) &*&
  malloc_block_stack(s);
@*/

// TODO: make this function pass the verification
/* get_destructor function
-params: A stack

It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
/*@
  requires stack(stack, ?size);
  ensures stack(stack, size) &*& result == ?d &*& stack->destructor |-> d;
@*/
{
  //@ open stack(stack, size);
  destructor* d = stack->destructor;
  //@ close stack(stack, size);
  return d;
}