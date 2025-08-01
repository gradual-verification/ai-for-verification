#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*& a->count |-> c;
@*/

// TODO: make this function pass the verification
void subtract(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c);
  //@ ensures Accumulator(a, t - x, c + 1);
{
  a->total -= x;
  a->count += 1;
}
