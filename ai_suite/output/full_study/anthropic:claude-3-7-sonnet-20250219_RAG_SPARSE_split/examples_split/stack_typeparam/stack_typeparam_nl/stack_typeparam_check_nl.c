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
// Predicate for data structure
predicate data_structure(struct data* d) =
  d->foo |-> ?f &*& d->bar |-> ?b &*& malloc_block_data(d);

// Predicate for a single node in the stack
predicate node(struct node* n, destructor* d) =
  n->data |-> ?data &*& n->next |-> ?next &*&
  malloc_block_node(n) &*&
  data_structure(data) &*&
  (next == 0 ? true : node(next, d));

// Predicate for the stack
predicate stack(struct stack* s, int size) =
  s->first |-> ?first &*&
  s->destructor |-> ?d &*&
  s->size |-> size &*&
  malloc_block_stack(s) &*&
  (first == 0 ? size == 0 : node(first, d));
@*/

/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
//@ requires is_destructor(destructor) == true;
//@ ensures stack(result, 0);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close stack(stack, 0);
  return stack;
}


/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
//@ requires stack(stack, ?size);
//@ ensures true;
{
  //@ open stack(stack, size);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
  //@ invariant current == 0 ? true : node(current, destructor);
  {
    //@ open node(current, destructor);
    struct node* next = current->next;
    //@ open data_structure(current->data);
    destructor(current->data);
    free(current);
    current = next;
  }
  free(stack);
}


/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
//@ requires stack(stack, ?size) &*& data_structure(data) &*& size < INT_MAX;
//@ ensures stack(stack, size + 1);
{
  //@ open stack(stack, size);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  
  //@ close node(node, stack->destructor);
  //@ close stack(stack, size + 1);
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
//@ requires stack(stack, ?size) &*& size > 0;
//@ ensures stack(stack, size - 1) &*& data_structure(result);
{
  //@ open stack(stack, size);
  struct node* first = stack->first;
  //@ open node(first, stack->destructor);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  //@ close stack(stack, size - 1);
  return data;
}


/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
//@ requires stack(stack, ?size);
//@ ensures stack(stack, size) &*& result == size;
{
  //@ open stack(stack, size);
  int size = stack->size;
  //@ close stack(stack, size);
  return size;
}


/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the fiven foo and bar.
*/
struct data* create_data(int foo, int bar)
//@ requires true;
//@ ensures data_structure(result) &*& result->foo |-> foo &*& result->bar |-> bar;
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  //@ close data_structure(data);
  return data;
}


/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data)
//@ requires data_structure(data);
//@ ensures true;
{
  //@ open data_structure(data);
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
  //@ assert s == 0;
  
  struct data* data = create_data(1, 2);
  push(stack, data);
  
  s = size(stack);
  //@ assert s == 1;
  
  data = create_data(2, 3);
  push(stack, data);

  s = size(stack);
  //@ assert s == 2;
  
  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}