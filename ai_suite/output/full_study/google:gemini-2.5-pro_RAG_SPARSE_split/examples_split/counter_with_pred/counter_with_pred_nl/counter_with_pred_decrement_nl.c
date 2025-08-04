#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate counter(struct Counter* c; int v) =
    c->value |-> v;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The decrement function decrements the value of the counter by 1.

@param c: a pointer to a Counter

The function makes sure that the counter has its value decremented by 1.
*/
void decrement(struct Counter* c)
    //@ requires counter(c, ?v) &*& INT_MIN < v;
    //@ ensures counter(c, v - 1);
{
  int tmp = c->value;
  c->value = tmp - 1;
}