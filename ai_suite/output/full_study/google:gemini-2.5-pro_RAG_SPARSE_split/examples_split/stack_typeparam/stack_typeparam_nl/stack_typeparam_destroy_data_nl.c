#include "stdlib.h"

// Forward declaration of the destructor type to make the C code valid.
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

/*@
// A predicate to represent ownership of a 'struct data'.
// It includes ownership of the fields and the memory block itself.
predicate data_struct(struct data *d; int foo, int bar) =
    d->foo |-> foo &*&
    d->bar |-> bar &*&
    malloc_block_data(d);
@*/


/*
  Destructors
*/

/*@
// A predicate family to abstract over the data that a destructor function can destroy.
// It is indexed by the function pointer of the destructor.
predicate_family data_to_destruct(void* destructor)(void* data);
@*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
    //@ requires data_to_destruct(this)(data);
    //@ ensures emp;


/*@
// An instance of the predicate family for the 'destroy_data' function.
// It specifies that 'destroy_data' knows how to destroy a 'struct data'.
predicate_family_instance data_to_destruct(destroy_data)(void* data) =
    data_struct((struct data*)data, _, _);
@*/

// TODO: make this function pass the verification
/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data) //@ : destructor
    //@ requires data_to_destruct(destroy_data)(data);
    //@ ensures emp;
{
    //@ open data_to_destruct(destroy_data)(data);
    //@ open data_struct(data, _, _);
    free(data);
}