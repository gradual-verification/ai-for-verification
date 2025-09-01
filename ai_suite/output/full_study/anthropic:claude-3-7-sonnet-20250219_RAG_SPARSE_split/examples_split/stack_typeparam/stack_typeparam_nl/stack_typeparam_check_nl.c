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
// Predicate for the data structure
predicate data_info(struct data* d; int foo, int bar) =
  d->foo |-> foo &*& d->bar |-> bar &*& malloc_block_data(d);

// Predicate for a single node in the stack
predicate node_info(struct node* n; void* data, struct node* next) =
  n->data |-> data &*& n->next |-> next &*& malloc_block_node(n);

// Predicate for a linked list of nodes
predicate nodes(struct node* first; list<void*> datas) =
  first == 0 ?
    datas == nil
  :
    node_info(first, ?data, ?next) &*& nodes(next, ?rest) &*& datas == cons(data, rest);

// Predicate for the stack structure
predicate stack(struct stack* s; list<void*> datas) =
  s->first |-> ?first &*& s->destructor |-> ?destructor &*& s->size |-> length(datas) &*&
  nodes(first, datas) &*& is_destructor(destructor) == true &*& malloc_block_stack(s);
@*/


/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
//@ requires is_destructor(destructor) == true;
//@ ensures stack(result, nil);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close nodes(0, nil);
  //@ close stack(stack, nil);
  return stack;
}


/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
//@ requires stack(stack, ?datas);
//@ ensures true;
{
  //@ open stack(stack, datas);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant nodes(current, ?remaining) &*& is_destructor(destructor) == true;
  {
    //@ open nodes(current, remaining);
    //@ open node_info(current, ?data, ?next);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(0, nil);
  free(stack);
}


/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
//@ requires stack(stack, ?datas) &*& stack->size < INT_MAX;
//@ ensures stack(stack, cons(data, datas));
{
  //@ open stack(stack, datas);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  
  //@ close node_info(node, data, stack->first);
  //@ close nodes(node, cons(data, datas));
  //@ close stack(stack, cons(data, datas));
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
//@ requires stack(stack, ?datas) &*& datas != nil &*& stack->size > INT_MIN;
//@ ensures stack(stack, tail(datas)) &*& result == head(datas);
{
  //@ open stack(stack, datas);
  //@ open nodes(stack->first, datas);
  //@ open node_info(stack->first, ?data, ?next);
  struct node* first = stack->first;
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  
  //@ close stack(stack, tail(datas));
  return data;
}


/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
//@ requires stack(stack, ?datas);
//@ ensures stack(stack, datas) &*& result == length(datas);
{
  //@ open stack(stack, datas);
  int size = stack->size;
  //@ close stack(stack, datas);
  return size;
}


/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the fiven foo and bar.
*/
struct data* create_data(int foo, int bar)
//@ requires true;
//@ ensures data_info(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  
  //@ close data_info(data, foo, bar);
  return data;
}


/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(void* data)
//@ requires data_info(data, _, _);
//@ ensures true;
{
  //@ open data_info(data, _, _);
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