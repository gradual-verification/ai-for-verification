#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

/*@
predicate Accumulator_(struct Accumulator *a; int total, int count) =
    a->total |-> total &*&
    a->count |-> count &*&
    malloc_block_Accumulator(a);
@*/

/***
 * Description:
 * The `average` function returns the average value of each operation. 
 * 
 * @param a: the given accumulator, which has its count > 0
 *
 * The function makes sure the accumulator is not changed, and the return value is total/count of this accumulator.
 */
int average(struct Accumulator* a)
    //@ requires Accumulator_(a, ?t, ?c) &*& c > 0;
    //@ ensures Accumulator_(a, t, c) &*& result == t / c;
{
    //@ open Accumulator_(a, t, c);
    int avg = a->total / a->count;
    //@ close Accumulator_(a, t, c);
    return avg;
}