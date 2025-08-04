#include "stdlib.h"

struct cell {
  int x;
};

/*@
// The predicate is made precise by separating the input parameter 'c'
// from the output parameter 'v' with a semicolon.
predicate cell(struct cell* c; int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/


// TODO: make this function pass the verification
void cell_set(struct cell* c, int v)
  //@ requires cell(c, _);
  //@ ensures cell(c, v);
{
  c->x = v;
}