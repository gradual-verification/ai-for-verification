#include "stdlib.h"
  
/*@
// Predicate family to represent ownership of the data stored in the stack.
// The family is indexed by the destructor function pointer.
predicate_family data_pred(void* destructor)(void* data);
@*/

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
// Predicate for a linked list of nodes.
// It holds a list of data pointers `ds`.
// For each data pointer `d_ptr` in `ds`, it also holds `data_pred(destr)(d_ptr)`.
predicate nodes(struct node* n, destructor* destr, list<void*> ds) =
  n == 0 ?
    ds == nil
  :
    n->data |-> ?d_ptr &*&
    n->next |-> ?next &*&
    malloc_block_node(n) &*&
    data_pred(destr)(d_ptr) &*&
    nodes(next, destr, ?ds_tail) &*&
    ds == cons(d_ptr, ds_tail);

// Predicate for the stack structure.
predicate stack(struct stack* s; destructor* d, list<void*> ds) =
  s->first |-> ?first &*&
  s->destructor |-> d &*&
  s->size |-> length(ds) &*&
  malloc_block_stack(s) &*&
  is_destructor(d) == true &*&
  nodes(first, d, ds);
@*/


/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};



/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
  //@ requires stack(stack, ?d, ?ds) &*& ds != nil;
  //@ ensures stack(stack, d, tail(ds)) &*& data_pred(d)(result);
{
  //@ open stack(stack, d, ds);
  struct node* first = stack->first;
  //@ open nodes(first, d, ds);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    //@ assert length(ds) >= 1;
    //@ assert false;
    abort();
  }
  stack->size--;
  //@ close stack(stack, d, tail(ds));
  return data;
}


/* get_destructor function
-params: A stack

It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
  //@ requires stack(stack, ?d, ?ds);
  //@ ensures stack(stack, d, ds) &*& result == d &*& is_destructor(d) == true;
{
  //@ open stack(stack, d, ds);
  destructor* d_res = stack->destructor;
  //@ close stack(stack, d, ds);
  return d_res;
}


// TODO: make this function pass the verification
/* pop_destroy function
-params: A stack
It makes sure to pop the top element from the stack and destroys it*/
void pop_destroy(struct stack* stack)
  //@ requires stack(stack, ?d, ?ds) &*& ds != nil;
  //@ ensures stack(stack, d, tail(ds));
{
  void* data = pop(stack);
  destructor* d_func = get_destructor(stack);
  d_func(data);
}