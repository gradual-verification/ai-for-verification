#include "stdlib.h"
  

/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

/*@
predicate node(struct node* n, void* data, struct node* next) =
  n->data |-> data &*& n->next |-> next &*& malloc_block_node(n);

predicate nodes(struct node* first, list<void*> datas, destructor* d) =
  first == 0 ?
    datas == nil
  :
    first != 0 &*& node(first, ?data, ?next) &*& 
    nodes(next, ?tail_datas, d) &*& 
    datas == cons(data, tail_datas);
@*/

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

/*@
predicate stack(struct stack* s, list<void*> datas, destructor* d, int size) =
  s->first |-> ?first &*& 
  s->destructor |-> d &*& 
  s->size |-> size &*& 
  malloc_block_stack(s) &*& 
  nodes(first, datas, d) &*& 
  size == length(datas) &*& 
  size >= 0;
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
//@ requires true;
//@ ensures true;


// TODO: make this function pass the verification
/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
//@ requires stack(stack, ?datas, ?d, ?size) &*& size > 0;
//@ ensures stack(stack, tail(datas), d, size - 1) &*& result == head(datas);
{
  //@ open stack(stack, datas, d, size);
  struct node* first = stack->first;
  //@ open nodes(first, datas, d);
  //@ assert first != 0;
  //@ open node(first, ?data, ?next);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  //@ close stack(stack, tail(datas), d, size - 1);
  return data;
}