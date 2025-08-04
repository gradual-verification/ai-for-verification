#include "stdlib.h"

struct Counter {
  int value;
};

/*@
// The predicate is updated to include the malloc_block, representing full ownership.
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/


// TODO: make this function pass the verification
struct Counter* init(int v)
  //@ requires true;
  //@ ensures Counter(result, v);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  //@ close Counter(c, v);
  return c;
}