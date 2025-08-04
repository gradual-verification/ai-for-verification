#include "stdlib.h"
#include "limits.h"
  

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
//@ requires owned_data(this)(data);
//@ ensures true;

/*@
// Predicate family to represent abstract ownership of data, indexed by the destructor function.
predicate_family owned_data(destructor* dtor)(void* data);

// Predicate for a linked list of nodes, holding the data and its ownership.
predicate nodes(struct node *n, destructor* dtor, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?d &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        (dtor == 0 ? true : owned_data(dtor)(d)) &*&
        nodes(next, dtor, ?rest_vs) &*&
        vs == cons(d, rest_vs);

// Predicate for the stack structure.
predicate stack(struct stack *s; destructor* dtor, list<void*> vs) =
    s->first |-> ?f &*&
    s->destructor |-> dtor &*&
    s->size |-> ?sz &*&
    malloc_block_stack(s) &*&
    (dtor == 0 ? true : is_destructor(dtor) == true) &*&
    nodes(f, dtor, vs) &*&
    sz == length(vs);
@*/


// TODO: make this function pass the verification
/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
    //@ requires stack(stack, ?dtor, ?vs) &*& (dtor == 0 ? true : owned_data(dtor)(data)) &*& length(vs) < INT_MAX;
    //@ ensures stack(stack, dtor, cons(data, vs));
{
  //@ open stack(stack, dtor, vs);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  //@ close nodes(node, dtor, cons(data, vs));
  //@ close stack(stack, dtor, cons(data, vs));
}