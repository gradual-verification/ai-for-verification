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
int average(struct Accumulator* a)
//@ requires a != 0 &*& a->total |-> ?t &*& a->count |-> ?c &*& c > 0;
//@ ensures a->total |-> t &*& a->count |-> c &*& result == t / c;
{
  int avg = a->total / a->count;
  return avg;
}