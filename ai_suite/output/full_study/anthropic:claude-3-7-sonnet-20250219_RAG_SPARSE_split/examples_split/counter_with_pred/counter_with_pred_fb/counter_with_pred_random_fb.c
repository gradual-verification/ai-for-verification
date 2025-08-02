bool random();
//@ requires true;
//@ ensures true;
#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v;
@*/


bool random()
//@ requires true;
//@ ensures true;
{
    // Since the specification doesn't constrain the return value,
    // we can return any boolean value
    return false; // or true, doesn't matter
}