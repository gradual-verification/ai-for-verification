#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate counter(struct Counter* c; int v) =
    c->value |-> v &*& malloc_block_Counter(c);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The init function creates a new counter with the given value.

@param v: the given value to be set

The function makes sure that the returned value is an counter whose value is v.
*/
struct Counter* init(int v)
    //@ requires true;
    //@ ensures counter(result, v);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;

  return c;
}