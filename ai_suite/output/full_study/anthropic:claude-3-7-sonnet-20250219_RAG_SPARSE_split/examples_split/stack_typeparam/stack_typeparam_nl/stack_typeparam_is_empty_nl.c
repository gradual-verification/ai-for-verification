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


// TODO: make this function pass the verification
/* is_empty function
-params: A stack
This function makes sure to checks if the stack is empty and does not modify the stack. */

/*@
// Define a predicate for nodes in the stack
predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        node->data |-> ?data &*& node->next |-> ?next &*& malloc_block_node(node) &*& nodes(next, count - 1);

// Define a predicate for the stack structure
predicate stack(struct stack *stack, int count) =
    stack != 0 &*&
    stack->first |-> ?first &*& 
    stack->destructor |-> ?destructor &*& 
    stack->size |-> count &*& 
    malloc_block_stack(stack) &*& 
    nodes(first, count);
@*/

bool is_empty(struct stack* stack)
//@ requires stack(stack, ?count);
//@ ensures stack(stack, count) &*& result == (count == 0);
{
    //@ open stack(stack, count);
    struct node* first = stack->first;
    //@ open nodes(first, count);
    bool result = first == 0;
    //@ close nodes(first, count);
    //@ close stack(stack, count);
    return result;
}