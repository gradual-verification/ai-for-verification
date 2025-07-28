#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v;
@*/


// TODO: make this function pass the verification
void dispose(struct Counter* c)
  //@ requires Counter(c, _);
  //@ ensures true;
{
  free(c);
}

