#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `destroy` function disposes a given accumulator.
 * 
 * @param a: the given accumulator
 *
 * The function makes sure the accumulator is freed. 
 */
void destroy(struct Accumulator* a)
{
  free(a);
}
