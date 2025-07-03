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
int current(struct Accumulator* a)
  /*@
  @ requires Accumulator(a, ?t, ?c);
  @ ensures Accumulator(a, t, c) &*& result == t;
  @*/
{
  int tmp = a->total;
  /*@
  @ open Accumulator(a, t, c);
  @*/
  /*@
  @ close Accumulator(a, t, c);
  @*/
  return tmp;
}