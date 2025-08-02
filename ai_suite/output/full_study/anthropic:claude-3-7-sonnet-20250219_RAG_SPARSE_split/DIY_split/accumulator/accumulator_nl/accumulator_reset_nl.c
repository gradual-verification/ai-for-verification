#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `reset` function resets the accumulator. 
 * 
 * @param a: the given accumulator
 *
 * The function makes sure the accumulator has the total and count of the accumulator to be 0.
 */
/*@
  // Define a predicate for the Accumulator struct
  predicate Accumulator(struct Accumulator *a; int total, int count) =
    a->total |-> total &*& a->count |-> count &*& malloc_block_Accumulator(a);
@*/

void reset(struct Accumulator* a)
//@ requires Accumulator(a, ?t, ?c);
//@ ensures Accumulator(a, 0, 0);
{
  //@ open Accumulator(a, t, c);
  a->total = 0;
  a->count = 0;
  //@ close Accumulator(a, 0, 0);
}