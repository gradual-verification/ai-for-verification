#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block(c, sizeof(struct Counter));
@*/

// TODO: make this function pass the verification
void dispose(struct Counter* c)
  //@ requires Counter(c, _);
  //@ ensures true;
{
  //@ open Counter(c, _);
  free(c);
}