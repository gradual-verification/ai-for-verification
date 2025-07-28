#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v;
@*/


// TODO: make this function pass the verification
bool random();
//@ requires true;
//@ ensures true;

