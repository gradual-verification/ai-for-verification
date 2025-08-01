#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

/*@
predicate Accumulator(struct Accumulator* a; int total, int count) =
    a->total |-> total &*& a->count |-> count;
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `add_multiple` function adds up the value in the accumulator with a given value for multiple times. 
 * 
 * @param a: the given accumulator
 * @param n: the number of times to add
 * @param x: the given value
 *
 * The function makes sure the accumulator has the total added by n*x and the count incremented by n.
 */
/*@
requires Accumulator(a, ?total, ?count) &*& n >= 0;
ensures Accumulator(a, total + n * x, count + n);
@*/
void add_multiple(struct Accumulator* a, int n, int x)
{
  int i = 0;
  while (i < n)
    //@ invariant Accumulator(a, total + i * x, count + i) &*& 0 <= i &*& i <= n;
  {
    a->total += x;
    a->count += 1;
    i++;
  }
}