#include "stdlib.h"
#include "limits.h"
  

/*
  Destructors
*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
//@ predicate_family data_inv(destructor* destructor)(void* data);
typedef void destructor(void* data);
//@ requires data_inv(this)(data);
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
predicate nodes(struct node *n, destructor* destructor, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?d &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        (destructor == 0 ? true : data_inv(destructor)(d)) &*&
        nodes(next, destructor, ?vs_tail) &*&
        vs == cons(d, vs_tail);

predicate stack(struct stack* s; list<void*> vs, destructor* dest) =
    s->first |-> ?f &*&
    s->destructor |-> dest &*&
    s->size |-> ?sz &*&
    malloc_block_stack(s) &*&
    sz == length(vs) &*&
    nodes(f, dest, vs);
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
/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
//@ requires stack(stack, ?vs, ?dest) &*& (dest == 0 ? true : data_inv(dest)(data)) &*& length(vs) < INT_MAX;
//@ ensures stack(stack, cons(data, vs), dest);
{
  //@ open stack(stack, vs, dest);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  //@ close nodes(node, dest, cons(data, vs));
  //@ assert length(cons(data, vs)) == length(vs) + 1;
  //@ close stack(stack, cons(data, vs), dest);
}