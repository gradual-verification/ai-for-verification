#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

//@ predicate cell(struct cell* c; int x) = c->x |-> x &*& c->mutex |-> ?m &*& mutex(m, cell(c, x));

/*@
predicate_family_instance thread_run_data(get)(struct cell* c) =
  cell(c, _);
@*/

// TODO: make this function pass the verification
int get(struct cell* c)
  //@ requires cell(c, ?x);
  //@ ensures cell(c, x) &*& result == x;
{
  int res;
  mutex_acquire(c->mutex);
  //@ open cell(c, x);
  res = c->x;
  //@ close cell(c, x);
  mutex_release(c->mutex);
  return res;
}