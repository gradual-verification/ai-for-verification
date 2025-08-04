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

// A predicate family to represent ownership of the data stored in the stack.
// It is indexed by the destructor function pointer, allowing for generic data types.
predicate_family data_pred(void* destructor)(void* data);

// A recursive predicate to model the linked list of nodes.
// It owns the node structs and the data they point to (via data_pred).
predicate nodes(struct node *n, destructor* d, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        data_pred(d)(v) &*&
        nodes(next, d, ?t) &*&
        vs == cons(v, t);

// A predicate for the stack structure.
// It owns the stack struct and the list of nodes.
predicate stack(struct stack *s; destructor* d, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> d &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    is_destructor(d) == true &*&
    nodes(first, d, vs);

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
//@ ensures emp;



// TODO: make this function pass the verification
/* get_destructor function
-params: A stack

It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
    //@ requires [?f]stack(stack, ?d, ?vs);
    //@ ensures [f]stack(stack, d, vs) &*& result == d;
{
  destructor* d = stack->destructor;
  return d;
}