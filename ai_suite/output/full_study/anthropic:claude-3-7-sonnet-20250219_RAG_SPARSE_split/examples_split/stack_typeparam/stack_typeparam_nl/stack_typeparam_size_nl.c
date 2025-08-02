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
predicate stack(struct stack* stack; int size) =
    stack->first |-> ?first &*&
    stack->destructor |-> ?destructor &*&
    stack->size |-> size &*&
    malloc_block_stack(stack);
@*/

// TODO: make this function pass the verification
/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
/*@
    requires stack(stack, ?size);
    ensures stack(stack, size) &*& result == size;
@*/
{
  /*@ open stack(stack, size); @*/
  int size = stack->size;
  /*@ close stack(stack, size); @*/
  return size;
}