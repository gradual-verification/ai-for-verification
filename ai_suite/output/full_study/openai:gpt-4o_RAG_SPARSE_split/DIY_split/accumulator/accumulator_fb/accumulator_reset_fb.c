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
void reset(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures Accumulator(a, 0, 0);
{
  //@ open Accumulator(a, _, _);
  a->total = 0;
  a->count = 0;
  //@ close Accumulator(a, 0, 0);
}