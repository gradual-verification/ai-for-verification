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
// Predicate for a node in the stack
predicate node(struct node *n; void *data, struct node *next) =
    n != 0 &*&
    n->data |-> data &*&
    n->next |-> next &*&
    malloc_block_node(n);

// Predicate for a linked list of nodes
predicate nodes(struct node *first; list<void*> datas) =
    first == 0 ?
        datas == nil
    :
        node(first, ?data, ?next) &*&
        nodes(next, ?tail_datas) &*&
        datas == cons(data, tail_datas);

// Predicate for a stack
predicate stack(struct stack *stack; list<void*> datas) =
    stack != 0 &*&
    stack->first |-> ?first &*&
    stack->destructor |-> ?destructor &*&
    stack->size |-> length(datas) &*&
    nodes(first, datas) &*&
    is_destructor(destructor) == true &*&
    malloc_block_stack(stack);
@*/

// TODO: make this function pass the verification
/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack *stack)
//@ requires stack(stack, ?datas);
//@ ensures true;
{
  //@ open stack(stack, datas);
  struct node *current = stack->first;
  destructor* destructor = stack->destructor;
  
  while (current != 0)
    //@ invariant nodes(current, ?remaining_datas) &*& is_destructor(destructor) == true;
  {
    //@ open nodes(current, remaining_datas);
    //@ open node(current, _, _);
    struct node *next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(0, _);
  free(stack);
}