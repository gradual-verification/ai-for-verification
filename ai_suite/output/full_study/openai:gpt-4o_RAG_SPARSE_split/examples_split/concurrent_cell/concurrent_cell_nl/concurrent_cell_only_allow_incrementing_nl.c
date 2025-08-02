#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

/*@
predicate cell(struct cell* c; int x) =
  c->x |-> x &*& c->mutex |-> ?m &*& malloc_block_cell(c) &*&
  mutex(m, cell_mutex_inv(c)) &*&
  cell_mutex_inv(c)() &*&
  x >= 0;

predicate cell_mutex_inv(struct cell* c)() =
  c->x |-> ?x &*& x >= 0;
@*/

/*get function
-param: struct cell* c
-description: This get function retrieves the current value of the `x` field in the given cell structure in a thread-safe manner (using mutex). 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the value of `x`.
*/
int get(struct cell* c)
  //@ requires cell(c, ?x);
  //@ ensures cell(c, x) &*& result == x;
{
  int res;
  mutex_acquire(c->mutex);
  //@ open cell_mutex_inv(c)();
  res = c->x;
  //@ close cell_mutex_inv(c)();
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
  //@ requires cell(c, ?x);
  //@ ensures cell(c, ?x2) &*& x <= x2;
{
  int x1 = get(c);
  int x2 = get(c);
  assert(x1 <= x2);
}