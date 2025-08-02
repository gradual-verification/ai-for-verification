#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `average` function returns the average value of each operation. 
 * 
 * @param a: the given accumulator, which has its count > 0
 *
 * The function makes sure the accumulator is not changed, and the return value is total/count of this accumulator.
 */
//@ predicate Accumulator(struct Accumulator *a, int total, int count) = a->total |-> total &*& a->count |-> count;

int average(struct Accumulator* a)
  //@ requires Accumulator(a, ?total, ?count) &*& count > 0;
  //@ ensures Accumulator(a, total, count) &*& result == total / count;
{
  //@ open Accumulator(a, total, count);
  int avg = a->total / a->count;
  //@ close Accumulator(a, total, count);
  return avg;
}