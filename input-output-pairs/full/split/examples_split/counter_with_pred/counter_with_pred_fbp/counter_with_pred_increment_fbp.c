#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/


// TODO: make this function pass the verification
void increment(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v < INT_MAX;
  //@ ensures Counter(c, v+1);
{
  int tmp = c->value;
  c->value = tmp + 1;
}

