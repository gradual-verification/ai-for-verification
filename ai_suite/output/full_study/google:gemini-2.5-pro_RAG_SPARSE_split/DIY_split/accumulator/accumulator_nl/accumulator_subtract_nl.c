void subtract(struct Accumulator* a, int x)
{
  a->total -= x;
  a->count += 1;
}
#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

/*@
// Predicate to represent an Accumulator struct in memory.
// It holds the values of the 'total' and 'count' fields
// and the memory block for the struct itself.
predicate Accumulator(struct Accumulator *a; int total, int count) =
    a->total |-> total &*&
    a->count |-> count &*&
    malloc_block_Accumulator(a);
@*/

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
/*@
requires Accumulator(a, ?old_total, ?old_count);
ensures Accumulator(a, old_total - x, old_count + 1);
@*/
{
  a->total -= x;
  a->count += 1;
}