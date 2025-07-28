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
void increment(struct cell* c)
{
  mutex_acquire(c->mutex);
  if (c->x == INT_MAX) {
    abort();
  }
  c->x++;
  {
  
  }
  mutex_release(c->mutex);
}

