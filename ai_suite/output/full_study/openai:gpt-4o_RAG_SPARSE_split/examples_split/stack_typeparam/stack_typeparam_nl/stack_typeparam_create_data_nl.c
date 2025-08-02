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

//@ predicate data(struct data* d; int foo, int bar) = d->foo |-> foo &*& d->bar |-> bar &*& malloc_block_data(d);

// TODO: make this function pass the verification
/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the given foo and bar.
*/
//@ requires true;
//@ ensures result != 0 ? data(result, foo, bar) : true;
struct data* create_data(int foo, int bar)
{
  struct data* data = malloc(sizeof(struct data));
  if (data == 0) abort();
  
  data->foo = foo;
  data->bar = bar;
  //@ close data(data, foo, bar);
  return data;
}