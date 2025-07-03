#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*& a->count |-> c &*& malloc_block_Accumulator(a);
@*/

// TODO: make this function pass the verification
void destroy(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures true;
{
  //@ open Accumulator(a, _, _);
  free(a);
}