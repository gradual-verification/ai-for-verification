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
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data)
{
  free(data);
}

