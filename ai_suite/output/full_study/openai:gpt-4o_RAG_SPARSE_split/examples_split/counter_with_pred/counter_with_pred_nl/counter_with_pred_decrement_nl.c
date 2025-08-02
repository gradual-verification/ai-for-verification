#include "stdlib.h"

struct Counter {
  int value;
};

//@ predicate counter(struct Counter* c; int v) = c->value |-> v;

// TODO: make this function pass the verification
/***
 * Description:
The decrement function decrements the value of the counter by 1.

@param c: a pointer to a Counter

The function makes sure that the counter has its value decremented by 1.
*/
//@ requires counter(c, ?v);
//@ ensures counter(c, v - 1);
void decrement(struct Counter* c)
{
  //@ open counter(c, _);
  int tmp = c->value;
  c->value = tmp - 1;
  //@ close counter(c, tmp - 1);
}