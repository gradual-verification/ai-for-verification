#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};


// TODO: make this function pass the verification
/*get function
-param: struct cell* c
-description: This get function retrieves the current value of the `x` field in the given cell structure in a thread-safe manner (using mutex). 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the value of `x`.
*/
int get(struct cell* c)
//@ requires c != 0 &*& [?f]mutex(c->mutex, ?p) &*& p() == cell_x(c, ?v);
//@ ensures [f]mutex(c->mutex, p) &*& result == v;
{
  int res;
  mutex_acquire(c->mutex);
  //@ open cell_x(c, v);
  res = c->x;
  //@ close cell_x(c, v);
  mutex_release(c->mutex);
  return res;
}