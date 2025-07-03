#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*&
  a->count |-> c &*&
  malloc_block_Accumulator(a);
@*/

// verified version of average
int average(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c) &*& c > 0;
  //@ ensures  Accumulator(a, t, c) &*& result == t / c;
{
  //@ open Accumulator(a, t, c);
  int total = a->total;
  int count = a->count;
  int avg   = total / count;
  //@ close Accumulator(a, t, c);
  return avg;
}