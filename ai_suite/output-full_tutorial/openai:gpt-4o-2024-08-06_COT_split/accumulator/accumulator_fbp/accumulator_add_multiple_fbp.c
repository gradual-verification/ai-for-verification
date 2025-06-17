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
void add_multiple(struct Accumulator* a, int n, int x)
/*@
  requires Accumulator(a, ?t, ?c) 
           &*& n >= 1 &*& x >= 0
           &*& t + n * x <= INT_MAX
           &*& c + n <= INT_MAX;
@*/
/*@
  ensures Accumulator(a, t + n * x, c + n);
@*/
{
  int i = 0;
  /*@
  loop_invariant 0 <= i <= n &*& Accumulator(a, t + i * x, c + i);
  @*/
  while (i < n)
  /*@
  invariant 0 <= i <= n &*& Accumulator(a, t + i * x, c + i);
  @*/
  {
    a->total += x;
    a->count += 1;
    i++;
  }
}