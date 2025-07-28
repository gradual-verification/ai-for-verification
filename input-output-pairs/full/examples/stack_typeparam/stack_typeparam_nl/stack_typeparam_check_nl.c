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
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the fiven foo and bar.
*/
struct data* create_data(int foo, int bar)
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  return data;
}


/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data)
{
  free(data);
}


/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
{
  int size = stack->size;
  return size;
}


/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
{
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
{
  struct node* first = stack->first;
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  return data;
}


/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  return stack;
}


/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
{
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
  {
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  free(stack);
}


// TODO: make this function pass the verification
/*
  check function
  - params: none
  - description: This function creates a stack, pushes two data elements onto it, 
    and checks the size of the stack.
*/
void check()
{
  struct stack* stack = create_empty_stack(destroy_data);
  int s = size(stack);
  assert s == 0;
  
  struct data* data = create_data(1, 2);
  push(stack, data);
  
  s = size(stack);
  
  data = create_data(2, 3);
  push(stack, data);

  s = size(stack);
  assert s == 2;
  
  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}

