#include "stdlib.h"

struct cell {
  int x;
};

/*@
// The predicate must include malloc_block_cell(c) to represent that 'c' points to a 
// memory block allocated on the heap, which can be deallocated by 'free'.
predicate cell(struct cell* c, int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/


void cell_dispose(struct cell* c) 
  //@ requires cell(c, _);
  //@ ensures true;
{
  // To call free(c), we need to provide the memory chunks that prove 'c' is a 
  // valid memory block. The 'cell' predicate now provides these chunks.
  // We open the predicate to expose its contents to the verifier.
  //@ open cell(c, _);
  free(c);
}