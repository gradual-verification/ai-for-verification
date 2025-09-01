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
// Predicate for the node structure
predicate node(struct node *n, void *data) =
    n->data |-> data &*&
    n->next |-> ?next &*&
    malloc_block_node(n);

// Predicate for a linked list of nodes
predicate nodes(struct node *first, list<void *> datas) =
    first == 0 ?
        datas == nil
    :
        node(first, ?data) &*&
        nodes(first->next, ?rest_datas) &*&
        datas == cons(data, rest_datas);

// Predicate for the stack structure
predicate stack(struct stack *s, list<void *> datas) =
    s->first |-> ?first &*&
    s->destructor |-> ?d &*&
    s->size |-> ?size &*&
    malloc_block_stack(s) &*&
    nodes(first, datas) &*&
    size == length(datas) &*&
    is_destructor(d) == true;

// Predicate family for destructor functions
predicate_family destructor_data(void *destructor_func)(void *data);
@*/

// TODO: make this function pass the verification
/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
//@ requires stack(stack, ?datas) &*& stack != 0 &*& data != 0;
//@ ensures stack(stack, cons(data, datas));
{
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();
  
  //@ close node(node, data);
  node->data = data;
  node->next = stack->first;
  
  //@ open stack(stack, datas);
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  //@ close nodes(node, cons(data, datas));
  //@ close stack(stack, cons(data, datas));
}