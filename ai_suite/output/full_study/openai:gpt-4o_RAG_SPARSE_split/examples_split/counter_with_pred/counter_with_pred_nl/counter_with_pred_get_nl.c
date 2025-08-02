#include "stdlib.h"

// Define a predicate for the Counter structure
/*@
predicate counter(struct Counter *c; int value) =
    c->value |-> value &*& malloc_block_counter(c);
@*/

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
requires counter(c, ?v);
ensures counter(c, v) &*& result == v;
@*/
int get(struct Counter* c)
{
  int tmp = c->value;
  return tmp;
}