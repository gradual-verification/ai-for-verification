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
// Define predicates for the stack data structure
predicate node(struct node* n; void* data) =
  n != 0 &*&
  n->data |-> data &*&
  n->next |-> ?next &*&
  malloc_block_node(n);

predicate nodes(struct node* first, int count) =
  first == 0 ?
    count == 0
  :
    node(first, ?data) &*&
    first->next |-> ?next &*&
    nodes(next, count - 1);

predicate stack(struct stack* s, int count) =
  s != 0 &*&
  s->first |-> ?first &*&
  s->destructor |-> ?d &*&
  s->size |-> count &*&
  malloc_block_stack(s) &*&
  nodes(first, count);
@*/

// TODO: make this function pass the verification
/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
/*@
  requires stack(stack, ?count);
  ensures stack(stack, count) &*& result == count;
@*/
{
  /*@
  open stack(stack, count);
  @*/
  int size = stack->size;
  /*@
  close stack(stack, count);
  @*/
  return size;
}