#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

/*@
predicate Accumulator(struct Accumulator *a; int total, int count) =
    a->total |-> total &*&
    a->count |-> count &*&
    malloc_block_Accumulator(a);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `add` function adds up the value in the accumulator with a given value. 
 * 
 * @param a: the given accumulator 
 * @param x: the given value
 *
 * The function makes sure the accumulator has the total added by x and the count incremented by 1.
 */
void add(struct Accumulator* a, int x)
    //@ requires Accumulator(a, ?t, ?c) &*& INT_MIN <= t + x &*& t + x <= INT_MAX &*& c < INT_MAX;
    //@ ensures Accumulator(a, t + x, c + 1);
{
  a->total += x;
  a->count += 1;
}