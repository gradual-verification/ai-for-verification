#include "stdlib.h"
  
/*
  Destructors
*/

/*@
// A predicate family to represent ownership of the data pointed to by stack elements.
// The ownership is tied to the specific destructor function.
predicate_family data_resource(destructor* f, void* data);
@*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
    //@ requires data_resource(this, data);
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

// Predicate for a linked list of nodes, storing the data pointers in a ghost list.
predicate nodes(struct node *n, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?d &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?vs_tail) &*&
        vs == cons(d, vs_tail);

// Predicate for the stack structure.
// It owns the stack struct, the list of nodes, and the data resources for each element if a destructor is provided.
predicate stack(struct stack* s, destructor* d, list<void*> vs) =
    s->first |-> ?f &*&
    s->destructor |-> d &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    nodes(f, vs) &*&
    (d == 0 ?
        true
    :
        is_destructor(d) == true &*& foreach(vs, (data_resource)(d))
    );

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
/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
    //@ requires destructor == 0 || is_destructor(destructor) == true;
    //@ ensures stack(result, destructor, nil);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close nodes(0, nil);
  /*@
  if (destructor != 0) {
      close foreach(nil, (data_resource)(destructor));
  }
  @*/
  //@ close stack(stack, destructor, nil);
  
  return stack;
}