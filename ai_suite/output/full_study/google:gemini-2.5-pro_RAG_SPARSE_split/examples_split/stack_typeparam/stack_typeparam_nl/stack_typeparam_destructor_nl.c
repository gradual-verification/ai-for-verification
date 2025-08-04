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

/*@
// A predicate family to represent ownership of the generic data.
// It is indexed by the destructor function pointer.
predicate_family object(void *destructor)(void *data);
@*/

// TODO: make this function pass the verification
/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
    //@ requires object(this)(data);
    //@ ensures true;
