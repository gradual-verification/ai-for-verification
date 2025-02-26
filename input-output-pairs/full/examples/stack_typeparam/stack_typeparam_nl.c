#include "stdlib.h"

/*
  Destructors
*/

typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  

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

/* create_empty_stack function
-params: A destructor
-description: Creates an empty stack*/
struct stack* create_empty_stack/*@ <T> @*/(destructor* destructor)
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
-description: Destroys the stack*/
void destroy_stack/*@ <T> @*/(struct stack* stack)
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

/* push function
-params: A stack and a data element
-description: Pushes the data element onto the stack*/
void push/*@ <T> @*/(struct stack* stack, void* data)
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
-description: Pops the top element from the stack*/
void* pop/*@ <T> @*/(struct stack* stack)
  /*@
  requires Stack<T>(stack, ?destructor, ?Ownership, Cons(?head, ?info, ?tail));
  @*/
  /*@
  ensures Stack(stack, destructor, Ownership, tail) &*&
          Ownership(head, info) &*& result == head;
  @*/
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

/* get_destructor function
-params: A stack
-description: Returns the destructor of the stack*/
destructor* get_destructor/*@ <T> @*/(struct stack* stack)
{
  destructor* d = stack->destructor;
  return d;
}

/* pop_destroy function
-params: A stack
-description: Pops the top element from the stack and destroys it*/
void pop_destroy/*@ <T> @*/(struct stack* stack)
{
  void* data = pop(stack);
  destructor* d = get_destructor(stack);
  d(data);
}

/* is_empty function
-params: A stack
-description: Checks if the stack is empty*/
bool is_empty/*@ <T> @*/(struct stack* stack)
{
  struct node* first = stack->first;
  return first == 0;
}

/* size function
-params: A stack
-description: Initializes the size of the stack*/
int size/*@ <T> @*/(struct stack* stack)
{
  int size = stack->size;
  return size;
}



/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};

/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields.
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

/*
  check2 function
  - params: none
  - description: This function creates a stack, pushes two data elements onto it, 
    pops and destroys them, and finally destroys the stack.
*/
void check2()
{
  struct stack* stack = create_empty_stack(destroy_data);
  struct data* d1 = create_data(1, 1);
  struct data* d2 = create_data(2, 2);
  
  push(stack, d1);
  push(stack, d2);

  struct data* d = pop(stack);
  destroy_data(d);

  d = pop(stack);
  
  destroy_data(d);
  
  destroy_stack(stack);
}
