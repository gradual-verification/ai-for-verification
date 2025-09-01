#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

/*@
// Define a predicate for the cell structure
predicate cell(struct cell *c; int value) =
    c->x |-> value &*&
    c->mutex |-> ?m &*&
    mutex(m, cell_mutex_inv(c)) &*&
    malloc_block_cell(c);

// Define the mutex invariant for the cell
predicate_ctor cell_mutex_inv(struct cell *c)() =
    c->x |-> ?value;
@*/

/*get function
-param: struct cell* c
-description: This get function retrieves the current value of the `x` field in the given cell structure in a thread-safe manner (using mutex). 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the value of `x`.
*/
int get(struct cell* c)
//@ requires cell(c, ?value);
//@ ensures cell(c, ?new_value) &*& result == new_value &*& value <= new_value;
{
  int res;
  //@ open cell(c, value);
  mutex_acquire(c->mutex);
  //@ open cell_mutex_inv(c)();
  res = c->x;
  {
    //@ assert c->x |-> res;
  }
  //@ close cell_mutex_inv(c)();
  mutex_release(c->mutex);
  //@ close cell(c, res);
  return res;
}

// TODO: make this function pass the verification
/*only_allow_incrementing function
-param: struct cell* c
-description: This function checks that the value of the `x` field in the given cell structure
can only be incremented, not decremented or changed in any other way.

In the source code, it uses an assert statement to check whether the value is incremented only.
*/
void only_allow_incrementing(struct cell* c)
//@ requires cell(c, ?value);
//@ ensures cell(c, ?new_value) &*& value <= new_value;
{
  int x1 = get(c);
  //@ assert cell(c, ?mid_value) &*& value <= mid_value &*& x1 == mid_value;
  int x2 = get(c);
  //@ assert cell(c, ?new_value) &*& mid_value <= new_value &*& x2 == new_value;
  assert(x1 <= x2);
  //@ assert value <= mid_value &*& mid_value <= new_value;
  //@ assert value <= new_value;
}