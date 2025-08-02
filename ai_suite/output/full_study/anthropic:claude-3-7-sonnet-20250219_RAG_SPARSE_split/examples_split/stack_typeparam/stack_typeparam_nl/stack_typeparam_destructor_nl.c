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
/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
/*@
// Define a predicate family for the data that can be destructed
predicate_family data_pred(void *destructor)(void *data);

// Define the destructor function type with appropriate specifications
@*/
typedef void destructor(void* data);
//@ requires data_pred(this)(data);
//@ ensures emp;