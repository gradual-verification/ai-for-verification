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

// TODO: make this function pass the verification
int current(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c);
  //@ ensures  Accumulator(a, t, c) &*& result == t;
{
  //@ open Accumulator(a, t, c);     // expose the fields
  int tmp = a->total;               // read the total
  //@ close Accumulator(a, t, c);    // restore predicate
  return tmp;                       // return the value
}