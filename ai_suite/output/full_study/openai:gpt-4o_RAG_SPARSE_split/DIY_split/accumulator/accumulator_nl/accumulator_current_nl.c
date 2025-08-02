#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `current` function returns the total of a given accumulator. 
 * 
 * @param a: the given accumulator
 *
 * The function makes sure the accumulator is not modified, and the return value is the total field of the accumulator.
 */
//@ predicate Accumulator(struct Accumulator* a; int total, int count) =
//@   a->total |-> total &*& a->count |-> count;

int current(struct Accumulator* a)
  //@ requires Accumulator(a, ?total, ?count);
  //@ ensures Accumulator(a, total, count) &*& result == total;
{
  //@ open Accumulator(a, total, count);
  int tmp = a->total;
  //@ close Accumulator(a, total, count);
  return tmp;
}