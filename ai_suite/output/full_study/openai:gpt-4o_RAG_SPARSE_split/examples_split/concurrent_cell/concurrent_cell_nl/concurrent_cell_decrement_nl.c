#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

//@ predicate cell(struct cell *c; int x) = c->x |-> x &*& c->mutex |-> ?m &*& mutex(m, cell(c, x));

/*@
predicate_family_instance thread_run_data(decrement)(struct cell *c) =
    cell(c, ?x);
@*/

// TODO: make this function pass the verification
void decrement(struct cell* c)
    //@ requires cell(c, ?x) &*& x > INT_MIN;
    //@ ensures cell(c, x - 1);
{
  mutex_acquire(c->mutex);
  //@ open cell(c, x);
  if (c->x == INT_MIN) {
    abort();
  }
  c->x--;
  //@ close cell(c, x - 1);
  mutex_release(c->mutex);
}