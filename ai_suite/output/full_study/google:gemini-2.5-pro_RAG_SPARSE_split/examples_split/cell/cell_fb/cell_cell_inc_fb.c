#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v;
@*/


// TODO: make this function pass the verification
void cell_inc(struct cell* c, int v)
  //@ requires cell(c, ?x) &*& INT_MIN <= x + v &*& x + v <= INT_MAX;
  //@ ensures cell(c, x + v);
{
  c->x += v;
}