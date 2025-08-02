#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

/*@
  // Define a predicate for the Accumulator structure
  predicate Accumulator(struct Accumulator *a; int total, int count) =
    a->total |-> total &*& a->count |-> count &*& malloc_block_Accumulator(a);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `current` function returns the total of a given accumulator. 
 * 
 * @param a: the given accumulator
 *
 * The function makes sure the accumulator is not modified, and the return value is the total field of the accumulator.
 */
int current(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c);
  //@ ensures Accumulator(a, t, c) &*& result == t;
{
  //@ open Accumulator(a, t, c);
  int tmp = a->total;
  //@ close Accumulator(a, t, c);
  return tmp;
}