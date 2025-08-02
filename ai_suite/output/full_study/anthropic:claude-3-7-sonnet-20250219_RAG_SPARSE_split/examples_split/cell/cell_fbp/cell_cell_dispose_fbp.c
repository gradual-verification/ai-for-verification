#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/


// TODO: make this function pass the verification
void cell_dispose(struct cell* c) 
  //@ requires cell(c, _);
  //@ ensures true;
{
  //@ open cell(c, _);
  free(c);
}