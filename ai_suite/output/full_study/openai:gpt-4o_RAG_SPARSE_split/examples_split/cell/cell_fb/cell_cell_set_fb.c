#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v;
@*/

// TODO: make this function pass the verification
void cell_set(struct cell* c, int v)
  //@ requires cell(c, _);
  //@ ensures cell(c, v);
{
  //@ open cell(c, _);
  c->x = v;
  //@ close cell(c, v);
}