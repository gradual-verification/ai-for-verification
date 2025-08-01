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
 * The function makes sure the accumulator has the total subtracted by x and the count decremented by 1.
 */
void subtract(struct Accumulator* a, int x)
{
  a->total -= x;
  a->count += 1;
}
