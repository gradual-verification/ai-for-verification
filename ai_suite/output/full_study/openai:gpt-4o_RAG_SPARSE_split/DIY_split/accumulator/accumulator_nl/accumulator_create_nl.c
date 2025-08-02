#include "stdlib.h"

// the field count keeps track of how many times add/subtract has been called
struct Accumulator {
  int total;
  int count; 
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `create` function creates a new accumulator with the given value.
 *
 * @param val: the given value
 *
 * The function makes sure that the created accumulator has total as val and its count as 1. 
 */
/*@
predicate Accumulator(struct Accumulator* a; int total, int count) =
    a->total |-> total &*& a->count |-> count &*& malloc_block_Accumulator(a);
@*/

struct Accumulator* create(int v)
    //@ requires true;
    //@ ensures result != 0 ? Accumulator(result, v, 1) : true;
{
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  if (a == 0) {
    abort();
  }
  a->total = v;
  a->count = 1;
  //@ close Accumulator(a, v, 1);
  return a;
}