#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

//@ predicate_ctor cell_inv(struct cell* c)() = c->x |-> ?value;

// TODO: make this function pass the verification
/*decrement function
-param: struct cell* c
-description: This function decrements field x in the given cell c in a thread-safe manner (using mutex).

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 
*/
void decrement(struct cell* c)
//@ requires c != 0 &*& [?f]c->mutex |-> ?m &*& [?g]mutex(m, cell_inv(c));
//@ ensures c != 0 &*& [f]c->mutex |-> m &*& [g]mutex(m, cell_inv(c));
{
  mutex_acquire(c->mutex);
  //@ open cell_inv(c)();
  if (c->x == INT_MIN) {
    abort();
  }
  c->x--;
  {
    //@ close cell_inv(c)();
  }
  mutex_release(c->mutex);
}