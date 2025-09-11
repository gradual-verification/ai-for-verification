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
predicate data_structure(struct data* data; int foo, int bar) =
  data->foo |-> foo &*& data->bar |-> bar &*& malloc_block_data(data);

// Predicate for a single node in the stack
predicate node(struct node* n; void* data) =
  n->data |-> data &*& n->next |-> ?next &*& malloc_block_node(n) &*& 
  next == 0 ? true : node(next, _);

// Predicate for the stack structure
predicate stack(struct stack* s; destructor* d) =
  s->first |-> ?first &*& s->destructor |-> d &*& s->size |-> ?size &*&
  malloc_block_stack(s) &*& 
  first == 0 ? size == 0 : node(first, _) &*& size > 0;

// Predicate for destructor function
predicate_family destructor_data(void* destructor)(void* data);

// Specific instance for our data destructor
predicate_family_instance destructor_data(destroy_data)(void* data) =
  data_structure(data, _, _);
@*/


/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
//@ requires is_destructor(destructor) == true;
//@ ensures stack(result, destructor);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close stack(stack, destructor);
  return stack;
}


/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
//@ requires stack(stack, ?destructor);
//@ ensures true;
{
  //@ open stack(stack, destructor);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant current == 0 ? true : node(current, _) &*& is_destructor(destructor) == true;
  {
    //@ open node(current, _);
    struct node* next = current->next;
    //@ close destructor_data(destructor)(current->data);
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
//@ requires stack(stack, ?destructor) &*& destructor_data(destructor)(data);
//@ ensures stack(stack, destructor);
{
  //@ open stack(stack, destructor);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  
  //@ close node(node, data);
  //@ close stack(stack, destructor);
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
//@ requires stack(stack, ?destructor) &*& stack->first != 0;
//@ ensures stack(stack, destructor) &*& destructor_data(destructor)(result);
{
  //@ open stack(stack, destructor);
  struct node* first = stack->first;
  //@ open node(first, _);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  //@ close stack(stack, destructor);
  return data;
}


/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the fiven foo and bar.
*/
struct data* create_data(int foo, int bar)
//@ requires true;
//@ ensures data_structure(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  //@ close data_structure(data, foo, bar);
  return data;
}


/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data) //@ : destructor
//@ requires destructor_data(destroy_data)(data);
//@ ensures true;
{
  //@ open destructor_data(destroy_data)(data);
  //@ open data_structure(data, _, _);
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
  struct stack* stack = create_empty_stack(destroy_data);
  struct data* d1 = create_data(1, 1);
  struct data* d2 = create_data(2, 2);
  
  //@ close destructor_data(destroy_data)(d1);
  push(stack, d1);
  //@ close destructor_data(destroy_data)(d2);
  push(stack, d2);

  struct data* d = pop(stack);
  //@ open destructor_data(destroy_data)(d);
  destroy_data(d);

  d = pop(stack);
  //@ open destructor_data(destroy_data)(d);
  destroy_data(d);
  
  destroy_stack(stack);
}