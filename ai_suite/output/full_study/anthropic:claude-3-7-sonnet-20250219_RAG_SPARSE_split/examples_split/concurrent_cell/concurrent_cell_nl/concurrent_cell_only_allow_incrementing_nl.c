#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};


/*get function
-param: struct cell* c
-description: This get function retrieves the current value of the `x` field in the given cell structure in a thread-safe manner (using mutex). 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the value of `x`.
*/
int get(struct cell* c)
//@ requires c != 0 &*& [?f]mutex(c->mutex, ?inv) &*& inv() &*& [?f2]c->x |-> ?x;
//@ ensures [f]mutex(c->mutex, inv) &*& inv() &*& [f2]c->x |-> ?new_x &*& result == new_x;
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  {
  }
  mutex_release(c->mutex);
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
//@ requires c != 0 &*& [?f]mutex(c->mutex, ?inv) &*& inv();
//@ ensures [f]mutex(c->mutex, inv) &*& inv();
{
  int x1 = get(c);
  //@ open inv();
  //@ close inv();
  int x2 = get(c);
  assert x1 <= x2;
}