#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/


// TODO: make this function pass the verification
int cell_get(struct cell* c)
  //@ requires cell(c, ?v);
  //@ ensures cell(c, v) &*& result == v;
{
  return c->x;
}

