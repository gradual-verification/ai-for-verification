#include "stdlib.h"

struct Counter {
  int value;
};

//@ predicate counter(struct Counter* c; int v) = c->value |-> v &*& malloc_block_counter(c);

// TODO: make this function pass the verification
/***
 * Description:
The dispose function frees the memory allocated for the Counter.

@param c: a pointer to a Counter

The function makes sure that the counter c is freed.
*/
void dispose(struct Counter* c)
  //@ requires counter(c, _);
  //@ ensures true;
{
  free(c);
}