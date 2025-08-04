#include "stdlib.h"
//@ #include "list.gh"
  

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
    //@ requires true;
    //@ ensures true;

/*@

predicate nodes(struct node *n, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?d &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?rest) &*&
        vs == cons(d, rest);

predicate stack(struct stack *s, list<void*> vs, destructor* dtor) =
    s->first |-> ?f &*&
    s->destructor |-> dtor &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    nodes(f, vs);

@*/


// TODO: make this function pass the verification
/* is_empty function
-params: A stack
This function makes sure to checks if the stack is empty and does not modify the stack. */
bool is_empty(struct stack* stack)
    //@ requires stack(stack, ?vs, ?dtor);
    //@ ensures stack(stack, vs, dtor) &*& result == (vs == nil);
{
  //@ open stack(stack, vs, dtor);
  struct node* first = stack->first;
  //@ open nodes(first, vs);
  //@ close nodes(first, vs);
  //@ close stack(stack, vs, dtor);
  return first == 0;
}