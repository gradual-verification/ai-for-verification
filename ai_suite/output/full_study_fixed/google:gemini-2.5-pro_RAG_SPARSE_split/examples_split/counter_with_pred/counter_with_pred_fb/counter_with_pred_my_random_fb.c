#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v;
@*/

//@ fixpoint bool random_bool();

bool my_random()
//@ requires true;
//@ ensures true;
{
    if (random_bool()) {
        return true;
    } else {
        return false;
    }
}