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
//@ predicate_family data_pred(void *func)(void *data);
//@ requires data_pred(this)(data);
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

predicate nodes(struct node *n, destructor *d, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*& n->next |-> ?next &*&
        malloc_block_node(n) &*&
        data_pred(d)(data) &*&
        nodes(next, d, ?tail_vs) &*&
        vs == cons(data, tail_vs);

predicate stack(struct stack *s; destructor *d, list<void*> vs) =
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



// TODO: make this function pass the verification
/* get_destructor function
-params: A stack

It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
    //@ requires stack(stack, ?d, ?vs);
    //@ ensures stack(stack, d, vs) &*& result == d;
{
  //@ open stack(stack, d, vs);
  destructor* d = stack->destructor;
  //@ close stack(stack, d, vs);
  return d;
}