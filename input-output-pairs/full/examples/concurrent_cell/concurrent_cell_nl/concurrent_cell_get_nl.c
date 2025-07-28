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
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  {
  }
  mutex_release(c->mutex);
  return res;
}

