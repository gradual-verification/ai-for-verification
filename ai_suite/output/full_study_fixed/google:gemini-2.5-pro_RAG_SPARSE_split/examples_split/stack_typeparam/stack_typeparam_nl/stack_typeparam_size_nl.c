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

/*@

// A recursive predicate to model the linked list of nodes.
// It describes the shape of the list and collects the data pointers into a ghost list `vs`.
predicate nodes(struct node* n; list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?tail) &*&
        vs == cons(data, tail);

// A predicate to model the stack struct and its invariants.
// It owns the stack struct and the list of nodes.
// The invariant `s->size |-> length(vs)` is key to proving the correctness of the size function.
predicate stack(struct stack* s; destructor* dtor, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> dtor &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    nodes(first, vs);

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
/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
    //@ requires stack(stack, ?dtor, ?vs);
    //@ ensures stack(stack, dtor, vs) &*& result == length(vs);
{
    //@ open stack(stack, dtor, vs);
    int size = stack->size;
    //@ close stack(stack, dtor, vs);
    return size;
}