#include "stdlib.h"

/*
  Destructors
*/

/*@
// A predicate family to represent the data that the destructor is supposed to free.
// The family is indexed by the destructor function pointer itself.
predicate_family data_resource(void *destructor)(void *data);
@*/

// TODO: make this function pass the verification
/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
    //@ requires data_resource(this)(data);
    //@ ensures true;


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