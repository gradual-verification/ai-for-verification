#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/


// TODO: make this function pass the verification
void decrement(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v > INT_MIN;
  //@ ensures Counter(c, v - 1);
{
  //@ open Counter(c, v);
  int tmp = c->value;
  c->value = tmp - 1;
  //@ close Counter(c, v - 1);
}