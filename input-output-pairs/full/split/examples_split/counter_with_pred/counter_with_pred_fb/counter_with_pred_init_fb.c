#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v;
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

  return c;
}

