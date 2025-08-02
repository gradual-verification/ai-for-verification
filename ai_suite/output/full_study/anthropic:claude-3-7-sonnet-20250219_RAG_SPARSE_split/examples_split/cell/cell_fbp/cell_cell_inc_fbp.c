#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/


// TODO: make this function pass the verification
void cell_inc(struct cell* c, int v)
  //@ requires cell(c, ?x) &*& INT_MIN - v <= x &*& x <= INT_MAX - v;
  //@ ensures cell(c, x + v);
{
  //@ open cell(c, x);
  c->x += v;
  //@ close cell(c, x + v);
}