#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/


int get(struct Counter* c)
  //@ requires Counter(c, ?v);
  //@ ensures Counter(c, v) &*& result==v; 
{
  int tmp = c->value;
  return tmp;
}