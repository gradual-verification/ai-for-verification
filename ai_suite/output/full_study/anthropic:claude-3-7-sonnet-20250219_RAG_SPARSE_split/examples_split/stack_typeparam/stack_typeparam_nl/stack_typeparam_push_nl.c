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
// Define predicates for our data structures
predicate node(struct node* n; void* d) =
    n->data |-> d &*&
    n->next |-> _ &*&
    malloc_block_node(n);

// Recursive predicate for a linked list of nodes
predicate nodes(struct node* first; list<void*> datas) =
    first == 0 ?
        datas == nil
    :
        node(first, ?d) &*&
        first->next |-> ?next &*&
        nodes(next, ?rest) &*&
        datas == cons(d, rest);

// Predicate for the destructor function
predicate destructor_fn(destructor* d) = is_destructor(d) == true;

// Predicate for the stack structure
predicate stack(struct stack* s; list<void*> datas) =
    s->first |-> ?first &*&
    s->destructor |-> ?d &*&
    s->size |-> ?size &*&
    malloc_block_stack(s) &*&
    nodes(first, datas) &*&
    destructor_fn(d) &*&
    size == length(datas) &*&
    size <= INT_MAX;
@*/


// TODO: make this function pass the verification
/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
//@ requires stack(stack, ?datas) &*& pointer(data, _);
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