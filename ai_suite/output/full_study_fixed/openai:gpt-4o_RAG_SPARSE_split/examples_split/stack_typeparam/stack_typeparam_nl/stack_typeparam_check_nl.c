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

predicate nodes(struct node* n, int count) =
  n == 0 ? count == 0 : n->data |-> ?data &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, count - 1);

predicate stack(struct stack* stack, int count, destructor* destructor) =
  stack->first |-> ?first &*& stack->destructor |-> destructor &*& stack->size |-> count &*& malloc_block_stack(stack) &*& nodes(first, count);

predicate data(struct data* data, int foo, int bar) =
  data->foo |-> foo &*& data->bar |-> bar &*& malloc_block_data(data);

@*/

/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
  //@ requires true;
  //@ ensures stack(result, 0, destructor);
{
  struct stack* stack = malloc(sizeof(struct stack));
  if (stack == 0) abort();

  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;

  //@ close nodes(0, 0);
  //@ close stack(stack, 0, destructor);
  return stack;
}

/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
  //@ requires stack(stack, _, ?destructor);
  //@ ensures true;
{
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;

  while (current != 0)
    //@ invariant nodes(current, ?count);
  {
    //@ open nodes(current, count);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(0, _);
  free(stack);
}

/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
  //@ requires stack(stack, ?count, ?destructor) &*& data != 0;
  //@ ensures stack(stack, count + 1, destructor);
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
  //@ close nodes(node, count + 1);
  //@ close stack(stack, count + 1, destructor);
}

/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
  //@ requires stack(stack, ?count, ?destructor) &*& count > 0;
  //@ ensures stack(stack, count - 1, destructor) &*& result != 0;
{
  struct node* first = stack->first;
  //@ open nodes(first, count);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  //@ close stack(stack, count - 1, destructor);
  return data;
}

/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
  //@ requires stack(stack, ?count, ?destructor);
  //@ ensures stack(stack, count, destructor) &*& result == count;
{
  int size = stack->size;
  return size;
}

/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the given foo and bar.
*/
struct data* create_data(int foo, int bar)
  //@ requires true;
  //@ ensures data(result, foo, bar);
{
  struct data* data = malloc(sizeof(struct data));
  if (data == 0) abort();

  data->foo = foo;
  data->bar = bar;
  //@ close data(data, foo, bar);
  return data;
}

/*
  destroy_data function
  - params: data structure
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data)
  //@ requires data(data, _, _);
  //@ ensures true;
{
  //@ open data(data, _, _);
  free(data);
}

// TODO: make this function pass the verification
/*
  check function
  - params: none
  - description: This function creates a stack, pushes two data elements onto it, 
    and checks the size of the stack.
*/
void check()
  //@ requires true;
  //@ ensures true;
{
  struct stack* stack = create_empty_stack(destroy_data);
  int s = size(stack);
  assert(s == 0);

  struct data* data = create_data(1, 2);
  push(stack, data);

  s = size(stack);

  data = create_data(2, 3);
  push(stack, data);

  s = size(stack);
  assert(s == 2);

  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}