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
//@ requires pointer(data, ?p) &*& p != 0;
//@ ensures emp;


/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

//@ predicate node(struct node* n; void* d, struct node* next) = n->data |-> d &*& n->next |-> next &*& malloc_block_node(n);

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

//@ predicate nodes(struct node* n, int count; destructor* d) = n == 0 ? count == 0 : node(n, ?data, ?next) &*& pointer(data, ?p) &*& p != 0 &*& nodes(next, count - 1, d);
//@ predicate stack(struct stack* s; int count) = s->first |-> ?first &*& s->destructor |-> ?d &*& s->size |-> count &*& is_destructor(d) == true &*& nodes(first, count, d) &*& malloc_block_stack(s);


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
//@ requires stack(stack, ?count) &*& count > 0;
//@ ensures stack(stack, count - 1) &*& pointer(result, ?p) &*& p != 0;
{
  //@ open stack(stack, count);
  struct node* first = stack->first;
  //@ open nodes(first, count, ?d);
  //@ open node(first, ?data, ?next);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  //@ close stack(stack, count - 1);
  return data;
}


/* get_destructor function
-params: A stack

It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
//@ requires stack(stack, ?count);
//@ ensures stack(stack, count) &*& is_destructor(result) == true;
{
  //@ open stack(stack, count);
  destructor* d = stack->destructor;
  //@ close stack(stack, count);
  return d;
}


// TODO: make this function pass the verification
/* pop_destroy function
-params: A stack
It makes sure to pop the top element from the stack and destroys it*/
void pop_destroy(struct stack* stack)
//@ requires stack(stack, ?count) &*& count > 0;
//@ ensures stack(stack, count - 1);
{
  void* data = pop(stack);
  destructor* d = get_destructor(stack);
  d(data);
}