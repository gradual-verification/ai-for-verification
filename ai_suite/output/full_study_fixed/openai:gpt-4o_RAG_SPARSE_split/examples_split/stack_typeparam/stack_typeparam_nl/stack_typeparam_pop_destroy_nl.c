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

/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};

/*@

predicate nodes(struct node* n, list<void*> vs) =
  n == 0 ? 
    vs == nil 
  : 
    n->data |-> ?d &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(d, vs0);

predicate stack(struct stack* s, list<void*> vs) =
  s->first |-> ?f &*& s->destructor |-> ?d &*& s->size |-> ?size &*& malloc_block_stack(s) &*& nodes(f, vs) &*& length(vs) == size;

predicate is_destructor(destructor* d) = true;

@*/

/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
  //@ requires stack(stack, ?vs) &*& vs != nil;
  //@ ensures stack(stack, tail(vs)) &*& result == head(vs);
{
  //@ open stack(stack, vs);
  struct node* first = stack->first;
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  //@ close stack(stack, tail(vs));
  return data;
}

/* get_destructor function
-params: A stack
It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
  //@ requires stack(stack, ?vs);
  //@ ensures stack(stack, vs) &*& result == stack->destructor;
{
  //@ open stack(stack, vs);
  destructor* d = stack->destructor;
  //@ close stack(stack, vs);
  return d;
}

// TODO: make this function pass the verification
/* pop_destroy function
-params: A stack
It makes sure to pop the top element from the stack and destroys it*/
void pop_destroy(struct stack* stack)
  //@ requires stack(stack, ?vs) &*& vs != nil &*& is_destructor(stack->destructor);
  //@ ensures stack(stack, tail(vs));
{
  void* data = pop(stack);
  destructor* d = get_destructor(stack);
  d(data);
}