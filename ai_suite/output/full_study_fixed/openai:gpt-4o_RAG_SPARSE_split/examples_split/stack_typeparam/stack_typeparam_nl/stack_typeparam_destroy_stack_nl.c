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

predicate nodes(struct node *node, int count) =
    node == 0 ? count == 0 : 0 < count &*& node->data |-> ?data &*& node->next |-> ?next &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->first |-> ?first &*& stack->destructor |-> ?destructor &*& stack->size |-> count &*& malloc_block_stack(stack) &*& nodes(first, count);

@*/

// TODO: make this function pass the verification
/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
    //@ requires stack(stack, _);
    //@ ensures true;
{
    //@ open stack(stack, _);
    struct node* current = stack->first;
    destructor* destructor = stack->destructor;
  
    while (current != 0)
        //@ invariant nodes(current, _);
    {
        //@ open nodes(current, _);
        struct node* next = current->next;
        destructor(current->data);
        free(current);
        current = next;
    }
    //@ open nodes(0, _);
    free(stack);
}