#include "stdlib.h"

struct Counter {
  int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The get function gets the values of the given counter.

@param c: pointer to a Counter

The function makes sure that the counter c is unchanged and the return value is the value of c.
*/
/*@
// Define a predicate for a Counter structure
predicate counter(struct Counter* c; int value) =
    c->value |-> value &*& malloc_block_Counter(c);
@*/

int get(struct Counter* c)
//@ requires counter(c, ?v);
//@ ensures counter(c, v) &*& result == v;
{
  //@ open counter(c, v);
  int tmp = c->value;
  //@ close counter(c, v);
  return tmp;
}