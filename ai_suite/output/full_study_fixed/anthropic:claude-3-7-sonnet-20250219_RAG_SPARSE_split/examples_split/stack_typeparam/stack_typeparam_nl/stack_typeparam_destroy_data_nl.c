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


// TODO: make this function pass the verification
/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/

/*@
// Define a predicate for the data structure
predicate data_structure(struct data *data) =
    data->foo |-> _ &*&
    data->bar |-> _ &*&
    malloc_block_data(data);
@*/

void destroy_data(struct data* data)
//@ requires data_structure(data);
//@ ensures true;
{
  //@ open data_structure(data);
  free(data);
}