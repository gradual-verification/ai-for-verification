#include "stdlib.h"

/*@
// A predicate to represent an Accumulator struct in the heap.
// It takes the pointer 'a' and the logical values of its fields 'total' and 'count'.
predicate Accumulator(struct Accumulator *a; int total, int count) =
    // The predicate owns the memory for the 'total' field and knows its value.
    a->total |-> total &*&
    // The predicate owns the memory for the 'count' field and knows its value.
    a->count |-> count &*&
    // The predicate owns the malloc block for the entire struct.
    malloc_block_Accumulator(a);
@*/

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
void reset(struct Accumulator* a)
    //@ requires Accumulator(a, ?t, ?c);
    //@ ensures Accumulator(a, 0, 0);
{
  a->total = 0;
  a->count = 0;
}