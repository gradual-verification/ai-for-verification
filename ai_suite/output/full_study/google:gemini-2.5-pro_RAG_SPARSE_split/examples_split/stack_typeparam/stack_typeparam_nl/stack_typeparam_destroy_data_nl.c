#include "stdlib.h"
  
/*
  Destructors
*/

/*@
// A predicate family to specify the precondition of a destructor.
// The family is indexed by the function pointer of the destructor.
predicate_family destructor_pre(void* func)(void* data);

// A predicate family to specify the postcondition of a destructor.
predicate_family destructor_post(void* func)(void* data);
@*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
    //@ requires destructor_pre(this)(data);
    //@ ensures destructor_post(this)(data);


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
// Predicate describing a valid, allocated data struct.
predicate data_struct(struct data *d; int foo, int bar) =
    d->foo |-> foo &*&
    d->bar |-> bar &*&
    malloc_block_data(d);
@*/

/*@
// Instantiation of the destructor_pre predicate family for the destroy_data function.
// It requires ownership of a data_struct.
predicate_family_instance destructor_pre(destroy_data)(void* data) =
    data_struct(data, _, _);

// Instantiation of the destructor_post predicate family for the destroy_data function.
// It ensures nothing, as the memory is freed.
predicate_family_instance destructor_post(destroy_data)(void* data) =
    true;
@*/

// TODO: make this function pass the verification
/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data) //@ : destructor
    //@ requires destructor_pre(destroy_data)(data);
    //@ ensures destructor_post(destroy_data)(data);
{
    //@ open destructor_pre(destroy_data)(data);
    //@ open data_struct(data, _, _);
    free(data);
    //@ close destructor_post(destroy_data)(data);
}