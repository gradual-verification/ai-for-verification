#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

//@ predicate cell(struct cell* c; int x) = c->x |-> x &*& c->mutex |-> ?m &*& mutex(m, cell(c, x));

/*@
predicate_family_instance thread_run_data(increment)(struct cell* c) =
    cell(c, ?x);
@*/

// TODO: make this function pass the verification
/*increment function
-param: struct cell* c
-description: This function increments field x in the given cell c in a thread-safe manner (using mutex).

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 
*/
void increment(struct cell* c)
    //@ requires cell(c, ?x) &*& x < INT_MAX;
    //@ ensures cell(c, x + 1);
{
  mutex_acquire(c->mutex);
  //@ open cell(c, x);
  if (c->x == INT_MAX) {
    abort();
  }
  c->x++;
  //@ close cell(c, x + 1);
  mutex_release(c->mutex);
}