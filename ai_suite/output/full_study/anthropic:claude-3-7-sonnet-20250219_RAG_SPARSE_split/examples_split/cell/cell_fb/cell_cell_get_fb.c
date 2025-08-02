#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v;
@*/


int cell_get(struct cell* c)
  //@ requires cell(c, ?v);
  //@ ensures cell(c, v) &*& result == v;
{
  //@ open cell(c, v);
  int result = c->x;
  //@ close cell(c, v);
  return result;
}