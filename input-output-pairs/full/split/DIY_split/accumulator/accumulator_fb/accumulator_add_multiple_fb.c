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
void add_multiple(struct Accumulator* a, int n, int x)
/*@
  requires Accumulator(a, ?t, ?c) 
           &*& n >= 1 &*& x >= 0;
@*/
/*@
  ensures Accumulator(a, t + n * x, c + n);
@*/
{
  int i = 0;
  while (i < n)
  {
    a->total += x;
    a->count += 1;
    i++;
  }
}
