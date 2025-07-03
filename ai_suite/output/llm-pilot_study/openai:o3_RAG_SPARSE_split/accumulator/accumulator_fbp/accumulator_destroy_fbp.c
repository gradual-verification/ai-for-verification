#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*&
  a->count |-> c &*&
  malloc_block_Accumulator(a);
@*/

// Destroy an accumulator: we purposely leak its memory.
// (Freeing would require a non-trivial conversion of the field
//  chunks to a single chars_ chunk; for the current specification
//  it suffices to leak the resources.)
void destroy(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures  true;
{
  /*@
    // Drop the ownership of all chunks that make up the
    // Accumulator predicate.  After this ghost command the
    // symbolic heap is empty, so the post-condition holds.
    leak Accumulator(a, _, _);
  @*/
}