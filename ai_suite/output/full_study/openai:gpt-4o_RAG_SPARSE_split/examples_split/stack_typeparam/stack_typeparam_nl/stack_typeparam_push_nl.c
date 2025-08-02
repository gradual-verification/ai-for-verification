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

/*@
predicate nodes(struct node* n, list<void*> values) =
  n == 0 ? 
    values == nil 
  : 
    n->data |-> ?d &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?values0) &*& values == cons(d, values0);

predicate stack(struct stack* s, list<void*> values) =
  s->first |-> ?first &*& s->destructor |-> ?destructor &*& s->size |-> ?size &*& malloc_block_stack(s) &*& nodes(first, values) &*& size == length(values);
@*/

// TODO: make this function pass the verification
/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
  //@ requires stack(stack, ?values) &*& data != 0;
  //@ ensures stack(stack, cons(data, values));
{
  struct node* node = malloc(sizeof(struct node));
  if (node == 0) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  //@ close nodes(node, cons(data, values));
  //@ close stack(stack, cons(data, values));
}