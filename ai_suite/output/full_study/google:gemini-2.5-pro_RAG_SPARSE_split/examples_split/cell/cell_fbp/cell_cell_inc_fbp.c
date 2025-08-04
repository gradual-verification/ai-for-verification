#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/


void cell_inc(struct cell* c, int v)
  //@ requires cell(c, ?x) &*& INT_MIN - v <= x &*& x <= INT_MAX - v;
  //@ ensures cell(c, x + v);
{
  c->x += v;
}