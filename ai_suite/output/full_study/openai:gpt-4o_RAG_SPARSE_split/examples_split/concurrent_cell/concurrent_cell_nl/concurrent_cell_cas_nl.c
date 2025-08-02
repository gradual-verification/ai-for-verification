#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

//@ predicate cell(struct cell* c; int x) = c->x |-> x &*& c->mutex |-> ?m &*& mutex(m, cell(c, x));

/*@
predicate_family_instance thread_run_data(cas)(struct cell* c) =
  cell(c, ?x);
@*/

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
  //@ requires cell(c, ?x);
  //@ ensures cell(c, ?x2) &*& (x == old ? x2 == new : x2 == x) &*& result == x;
{
  int res;
  mutex_acquire(c->mutex);
  //@ open cell(c, x);
  res = c->x;
  if(c->x == old) {
    c->x = new;
    //@ close cell(c, new);
  } else {
    //@ close cell(c, x);
  }
  mutex_release(c->mutex);
  return res;
}