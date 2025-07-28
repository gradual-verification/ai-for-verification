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


// TODO: make this function pass the verification
/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
{
  int size = stack->size;
  return size;
}

