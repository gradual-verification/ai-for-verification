#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};


// TODO: make this function pass the verification
/*cas function
-param: struct cell* c, int old, int new
-description: This compare-and-swap function checks if the current value of `x` in the given cell c is equal to `old`.
If it is, the function updates `x` to `new`. This operation is thread-safe due to the use of a mutex. 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the original value of `x` before the operation.
*/
int cas(struct cell* c, int old, int new)
//@ requires c != 0 &*& c->x |-> ?value &*& c->mutex |-> ?m &*& [?f]mutex(m, ?inv);
//@ ensures c->x |-> (value == old ? new : value) &*& c->mutex |-> m &*& [f]mutex(m, inv) &*& result == value;
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  if(c->x == old) {
    c->x = new;
  }
  {
    
  }
  mutex_release(c->mutex);
  return res;
}