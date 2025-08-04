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

/*@
// Predicate for the data stored in the stack.
// It is parameterized by the destructor function, allowing different
// data types with different destructors to be stored.
predicate_family data_pred(destructor* destructor)(void* data);

// Predicate for a linked list of nodes.
// It owns the nodes, their links, and the data they point to.
predicate nodes(struct node* n, destructor* d, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*& n->next |-> ?next &*&
        malloc_block_node(n) &*&
        // The data predicate ensures ownership of the data.
        data_pred(d)(data) &*&
        nodes(next, d, ?rest) &*&
        vs == cons(data, rest);

// Predicate for the stack structure.
// It owns the stack struct and the list of nodes.
predicate stack(struct stack* s, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> ?d &*&
    s->size |-> ?size &*&
    malloc_block_stack(s) &*&
    // The destructor must be a valid function pointer.
    is_destructor(d) == true &*&
    nodes(first, d, vs) &*&
    size == length(vs);
@*/


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
//@ requires data_pred(this)(data);
//@ ensures true;


// TODO: make this function pass the verification
/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
    //@ requires is_destructor(destructor) == true;
    //@ ensures stack(result, nil);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close nodes(0, destructor, nil);
  //@ close stack(stack, nil);
  
  return stack;
}