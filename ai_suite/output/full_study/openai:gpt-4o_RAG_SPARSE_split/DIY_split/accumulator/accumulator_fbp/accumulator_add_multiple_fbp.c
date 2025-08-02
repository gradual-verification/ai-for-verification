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
  while (i < n)
  /*@
    invariant Accumulator(a, t + i * x, c + i) &*& 0 <= i &*& i <= n;
    decreases n - i;
  @*/
  {
    if (a->total > INT_MAX - x) abort(); // Prevent overflow
    if (a->count > INT_MAX - 1) abort(); // Prevent overflow
    a->total += x;
    a->count += 1;
    i++;
  }
}