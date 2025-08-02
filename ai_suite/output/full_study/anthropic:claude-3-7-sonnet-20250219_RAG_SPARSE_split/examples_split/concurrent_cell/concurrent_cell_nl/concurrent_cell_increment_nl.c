#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};


// TODO: make this function pass the verification
/*increment function
-param: struct cell* c
-description: This function increments field x in the given cell c in a thread-safe manner (using mutex).

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 
*/

/*@
// Define a predicate for the cell structure
predicate cell(struct cell *c; int value) =
    c->x |-> value &*&
    c->mutex |-> ?m &*&
    mutex(m, cell_mutex_inv(c)) &*&
    malloc_block_cell(c);

// Define the mutex invariant
predicate_ctor cell_mutex_inv(struct cell *c)() =
    c->x |-> ?value;
@*/

void increment(struct cell* c)
//@ requires cell(c, ?value);
//@ ensures cell(c, value < INT_MAX ? value + 1 : value);
{
  //@ open cell(c, value);
  mutex_acquire(c->mutex);
  //@ open cell_mutex_inv(c)();
  if (c->x == INT_MAX) {
    abort();
  }
  c->x++;
  {
    //@ assert c->x |-> ?new_value;
    //@ assert new_value == value + 1;
  }
  //@ close cell_mutex_inv(c)();
  mutex_release(c->mutex);
  //@ close cell(c, value < INT_MAX ? value + 1 : value);
}