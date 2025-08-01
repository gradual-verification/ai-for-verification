#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v;
@*/


// TODO: make this function pass the verification
void cell_dispose(struct cell* c) 
  //@ requires cell(c, _);
  //@ ensures true;
{

  free(c);
}

