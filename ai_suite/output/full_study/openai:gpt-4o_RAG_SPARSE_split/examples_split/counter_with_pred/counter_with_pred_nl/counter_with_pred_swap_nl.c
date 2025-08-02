#include "stdlib.h"

struct Counter {
  int value;
};

// TODO: make this function pass the verification
/***
 * Description:
The swap function swaps the values of the two Counters.

@param c1, c2: pointers to two Counter

The function makes sure that the two counters have their values swapped.
*/
//@ requires c1->value |-> ?v1 &*& c2->value |-> ?v2;
//@ ensures c1->value |-> v2 &*& c2->value |-> v1;
void swap(struct Counter* c1, struct Counter* c2)
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}