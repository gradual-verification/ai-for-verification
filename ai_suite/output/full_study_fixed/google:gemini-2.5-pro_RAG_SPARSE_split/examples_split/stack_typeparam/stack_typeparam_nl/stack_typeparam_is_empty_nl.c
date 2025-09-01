#include "stdlib.h"
#include "stdbool.h"

/*
  Destructors
*/

/*@
// A predicate family to represent ownership of the data pointed to by `void*`.
// The family is indexed by the destructor function pointer.
// This allows different stack instances to have different data types and
// different ways of freeing them.
predicate_family data_chunk(void* destructor)(void* data);
@*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
    //@ requires data_chunk(this)(data);
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
// A recursive predicate for a linked list of nodes.
// It models the list of data pointers as a ghost list `vs`.
predicate node_list(struct node* n, destructor* dtor, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?d &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        (dtor == 0 ? true : data_chunk(dtor)(d)) &*&
        node_list(next, dtor, ?rest) &*&
        vs == cons(d, rest);

// The main predicate for the stack.
// It owns the stack struct and the list of nodes.
predicate stack(struct stack* s; destructor* dtor, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> dtor &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    (dtor == 0 ? true : is_destructor(dtor) == true) &*&
    node_list(first, dtor, vs);
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
/* is_empty function
-params: A stack
This function makes sure to checks if the stack is empty and does not modify the stack. */
bool is_empty(struct stack* stack)
    //@ requires [?f]stack(stack, ?dtor, ?vs);
    //@ ensures [f]stack(stack, dtor, vs) &*& result == (vs == nil);
{
  //@ open stack(stack, dtor, vs);
  struct node* first = stack->first;
  //@ open node_list(first, dtor, vs);
  //@ close node_list(first, dtor, vs);
  //@ close stack(stack, dtor, vs);
  return first == 0;
}