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
struct Accumulator* create(int v)
  //@ requires true;
  //@ ensures Accumulator(result, v, 1);
{
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  //@ open Accumulator(a, _, _);
  if (a == 0) {
    abort();
  }
  a->total = v;
  a->count = 1;
  //@ close Accumulator(a, v, 1);
  return a;
}