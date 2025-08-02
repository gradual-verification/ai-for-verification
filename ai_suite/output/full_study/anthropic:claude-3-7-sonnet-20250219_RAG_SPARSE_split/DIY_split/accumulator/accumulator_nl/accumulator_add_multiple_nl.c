#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

/*@
// Define a predicate for the Accumulator structure
predicate accumulator(struct Accumulator *a, int total, int count) =
    a->total |-> total &*& a->count |-> count &*& malloc_block_Accumulator(a);
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
// Specification for add_multiple function
requires accumulator(a, ?old_total, ?old_count) &*& n >= 0;
ensures accumulator(a, old_total + n * x, old_count + n);
@*/
void add_multiple(struct Accumulator* a, int n, int x)
{
  int i = 0;
  //@ open accumulator(a, old_total, old_count);
  
  /*@
  // Loop invariant
  invariant a->total |-> old_total + i * x &*& a->count |-> old_count + i &*& 
            malloc_block_Accumulator(a) &*& 0 <= i &*& i <= n;
  @*/
  while (i < n)
  {
    a->total += x;
    a->count += 1;
    i++;
  }
  
  //@ close accumulator(a, old_total + n * x, old_count + n);
}