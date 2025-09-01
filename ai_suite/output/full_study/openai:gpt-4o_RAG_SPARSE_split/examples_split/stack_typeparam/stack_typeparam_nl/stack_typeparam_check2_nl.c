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
predicate nodes(struct node* n, predicate(void*; list<void*>) P, list<void*> vs) =
  n == 0 ? vs == nil : n->data |-> ?d &*& n->next |-> ?next &*& malloc_block_node(n) &*& P(d, ?v) &*& nodes(next, P, ?vs0) &*& vs == cons(d, vs0);

predicate stack(struct stack* s, predicate(void*; list<void*>) P, list<void*> vs) =
  s->first |-> ?first &*& s->destructor |-> ?destructor &*& s->size |-> ?size &*& malloc_block_stack(s) &*& nodes(first, P, vs) &*& length(vs) == size;

predicate data_pred(void* d, list<void*> v) = d == 0 ? v == nil : v == cons(d, nil);

@*/

/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
  //@ requires true;
  //@ ensures stack(result, data_pred, nil);
{
  struct stack* stack = malloc(sizeof(struct stack));
  if (stack == 0) abort();

  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;

  //@ close nodes(0, data_pred, nil);
  //@ close stack(stack, data_pred, nil);
  return stack;
}

/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
  //@ requires stack(stack, data_pred, ?vs);
  //@ ensures true;
{
  //@ open stack(stack, data_pred, vs);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;

  while (current != 0)
    //@ invariant nodes(current, data_pred, ?vs0);
  {
    //@ open nodes(current, data_pred, vs0);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(0, data_pred, _);
  free(stack);
}

/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
  //@ requires stack(stack, data_pred, ?vs) &*& data_pred(data, ?v);
  //@ ensures stack(stack, data_pred, cons(data, vs));
{
  //@ open stack(stack, data_pred, vs);
  struct node* node = malloc(sizeof(struct node));
  if (node == 0) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  stack->size++;
  //@ close nodes(node, data_pred, cons(data, vs));
  //@ close stack(stack, data_pred, cons(data, vs));
}

/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
  //@ requires stack(stack, data_pred, ?vs) &*& vs != nil;
  //@ ensures stack(stack, data_pred, tail(vs)) &*& data_pred(result, head(vs));
{
  //@ open stack(stack, data_pred, vs);
  struct node* first = stack->first;
  //@ open nodes(first, data_pred, vs);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  stack->size--;
  //@ close stack(stack, data_pred, tail(vs));
  return data;
}

/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the given foo and bar.
*/
struct data* create_data(int foo, int bar)
  //@ requires true;
  //@ ensures result->foo |-> foo &*& result->bar |-> bar &*& malloc_block_data(result);
{
  struct data* data = malloc(sizeof(struct data));
  if (data == 0) abort();

  data->foo = foo;
  data->bar = bar;
  return data;
}

/*
  destroy_data function
  - params: data structure
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data)
  //@ requires data->foo |-> _ &*& data->bar |-> _ &*& malloc_block_data(data);
  //@ ensures true;
{
  free(data);
}

// TODO: make this function pass the verification
/*
  check2 function
  - params: none
  - description: This function creates a stack, pushes two data elements onto it, 
    pops and destroys them, and finally destroys the stack.
*/
void check2()
  //@ requires true;
  //@ ensures true;
{
  struct stack* stack = create_empty_stack((destructor*)destroy_data);
  struct data* d1 = create_data(1, 1);
  struct data* d2 = create_data(2, 2);

  //@ close data_pred(d1, cons(d1, nil));
  //@ close data_pred(d2, cons(d2, nil));
  push(stack, d1);
  push(stack, d2);

  struct data* d = pop(stack);
  destroy_data(d);

  d = pop(stack);
  destroy_data(d);

  destroy_stack(stack);
}