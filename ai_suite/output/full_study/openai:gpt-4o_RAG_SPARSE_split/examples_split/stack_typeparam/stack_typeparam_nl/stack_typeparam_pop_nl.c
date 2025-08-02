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

predicate nodes(struct node* node, list<void*> values) =
    node == 0 ? 
        values == nil 
    : 
        node->data |-> ?data &*& node->next |-> ?next &*& malloc_block_node(node) &*& nodes(next, ?values0) &*& values == cons(data, values0);

predicate stack(struct stack* stack, list<void*> values) =
    stack->first |-> ?first &*& stack->destructor |-> ?destructor &*& stack->size |-> ?size &*& malloc_block_stack(stack) &*& nodes(first, values) &*& length(values) == size;

@*/

// TODO: make this function pass the verification
/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
    //@ requires stack(stack, ?values) &*& values != nil;
    //@ ensures stack(stack, tail(values)) &*& result == head(values);
{
    //@ open stack(stack, values);
    struct node* first = stack->first;
    //@ open nodes(first, values);
    void* data = first->data;
    stack->first = first->next;
    free(first);
    if (stack->size == INT_MIN) {
        abort();  // or handle error as necessary
    }
    stack->size--;
    //@ close stack(stack, tail(values));
    return data;
}