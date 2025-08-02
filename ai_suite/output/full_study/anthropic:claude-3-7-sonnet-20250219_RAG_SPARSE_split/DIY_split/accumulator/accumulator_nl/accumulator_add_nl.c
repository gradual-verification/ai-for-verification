#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

//@ predicate accumulator(struct Accumulator *a; int total, int count) = a->total |-> total &*& a->count |-> count &*& malloc_block_Accumulator(a);

/**
 * Description:
 * The `add` function adds up the value in the accumulator with a given value. 
 * 
 * @param a: the given accumulator 
 * @param x: the given value
 *
 * The function makes sure the accumulator has the total added by x and the count incremented by 1.
 */
void add(struct Accumulator* a, int x)
//@ requires accumulator(a, ?t, ?c);
//@ ensures accumulator(a, t + x, c + 1);
{
  //@ open accumulator(a, t, c);
  a->total += x;
  a->count += 1;
  //@ close accumulator(a, t + x, c + 1);
}