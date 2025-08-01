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



// TODO: make this function pass the verification
/* get_destructor function
-params: A stack

It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
{
  destructor* d = stack->destructor;
  return d;
}

