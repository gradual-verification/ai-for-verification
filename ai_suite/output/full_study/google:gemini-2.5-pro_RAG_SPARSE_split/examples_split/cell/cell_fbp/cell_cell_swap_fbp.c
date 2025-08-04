#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/


void cell_set(struct cell* c, int v)
  //@ requires cell(c, _);
  //@ ensures cell(c, v);
{
  c->x = v;
}


int cell_get(struct cell* c)
  //@ requires cell(c, ?v);
  //@ ensures cell(c, v) &*& result == v;
{
  return c->x;
}


// This function is correct as is and passes verification.
void cell_swap(struct cell* c1, struct cell* c2)
  //@ requires cell(c1, ?v1) &*& cell(c2, ?v2);
  //@ ensures cell(c1, v2) &*& cell(c2, v1);
{
  int tmp1 = cell_get(c1);
  int tmp2 = cell_get(c2);
  cell_set(c1, tmp2);
  cell_set(c2, tmp1);
}