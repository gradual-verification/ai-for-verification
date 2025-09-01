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
//@ requires true;
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
// Predicate for a linked list of nodes
predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        node->data |-> ?data &*& node->next |-> ?next &*& malloc_block_node(node) &*&
        nodes(next, count - 1);

// Predicate for a stack
predicate stack(struct stack *stack, int count) =
    stack->first |-> ?first &*& stack->destructor |-> ?destructor &*& stack->size |-> count &*&
    malloc_block_stack(stack) &*& nodes(first, count) &*&
    is_destructor(destructor) == true;
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
/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack *stack)
//@ requires stack(stack, ?count);
//@ ensures true;
{
  //@ open stack(stack, count);
  struct node *current = stack->first;
  destructor* destructor = stack->destructor;
  
  while (current != 0)
    //@ invariant nodes(current, ?remaining) &*& is_destructor(destructor) == true;
  {
    //@ open nodes(current, remaining);
    struct node *next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(0, _);
  free(stack);
}