#include "stdlib.h"

/*@
// Predicate for the data stored in the stack.
// It is a predicate family indexed by the destructor function pointer,
// allowing for generic data types with specific ownership rules.
predicate_family data_chunk(destructor* destructor)(void* data);
@*/
  

/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

/*@
// Predicate for a linked list of nodes.
// It represents the list of nodes starting from 'n'.
// 'd' is the destructor for the data in the nodes.
// 'vs' is a ghost list of the data pointers for functional correctness.
predicate nodes(struct node* n, destructor* d, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*& n->next |-> ?next &*&
        malloc_block_node(n) &*&
        data_chunk(d)(data) &*&
        nodes(next, d, ?rest) &*&
        vs == cons(data, rest);
@*/

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

/*@
// Predicate for the stack structure.
// 's' is the stack pointer.
// 'd' is the destructor for the data in the stack.
// 'vs' is a ghost list of the data pointers.
// It connects the concrete 'size' field to the length of the ghost list.
predicate stack(struct stack* s, destructor* d, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> d &*&
    s->size |-> ?sz &*&
    malloc_block_stack(s) &*&
    nodes(first, d, vs) &*&
    sz == length(vs);
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
    //@ requires data_chunk(this)(data);
    //@ ensures true;



// TODO: make this function pass the verification
/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
    //@ requires [?f]stack(stack, ?d, ?vs);
    //@ ensures [f]stack(stack, d, vs) &*& result == length(vs);
{
  //@ open [f]stack(stack, d, vs);
  int size = stack->size;
  //@ close [f]stack(stack, d, vs);
  return size;
}