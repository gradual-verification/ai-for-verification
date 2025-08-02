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
//@ requires a != 0 &*& a->total |-> _ &*& a->count |-> _;
//@ ensures a->total |-> 0 &*& a->count |-> 0;
void reset(struct Accumulator* a)
{
  a->total = 0;
  a->count = 0;
}