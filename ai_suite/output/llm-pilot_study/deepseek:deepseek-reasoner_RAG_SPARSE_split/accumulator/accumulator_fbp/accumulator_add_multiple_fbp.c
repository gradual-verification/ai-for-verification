#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*& a->count |-> c &*& malloc_block_Accumulator(a);
@*/

// Verified function with loop invariant
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
  while (i < n)
  /*@
    invariant Accumulator(a, t + i * x, c + i)
           &*& 0 <= i &*& i <= n
           &*& n >= 1 &*& x >= 0
           &*& t + n * x <= INT_MAX
           &*& c + n <= INT_MAX;
  @*/
  {
    //@ open Accumulator(a, t + i * x, c + i);
    a->total += x;
    a->count += 1;
    i++;
    //@ close Accumulator(a, t + i * x, c + i);
  }
}