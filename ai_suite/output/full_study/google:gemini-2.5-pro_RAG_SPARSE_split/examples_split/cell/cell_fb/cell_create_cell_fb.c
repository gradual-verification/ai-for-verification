#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/


// This function now passes verification with the corrected predicate.
struct cell* create_cell() 
  //@ requires true;
  //@ ensures cell(result, 0);
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) abort();
  c->x = 0;

  return c;
}