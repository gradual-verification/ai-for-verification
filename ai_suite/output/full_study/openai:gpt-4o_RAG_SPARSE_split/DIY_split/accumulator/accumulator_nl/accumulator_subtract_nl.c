#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `subtract` function subtracts the value in the accumulator by a given value. 
 * 
 * @param a: the given accumulator
 * @param x: the given value
 *
 * The function makes sure the accumulator has the total subtracted by x and the count incremented by 1.
 */
//@ predicate Accumulator(struct Accumulator *a; int total, int count) = a->total |-> total &*& a->count |-> count;

void subtract(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?total, ?count);
  //@ ensures Accumulator(a, total - x, count + 1);
{
  a->total -= x;
  a->count += 1;
}