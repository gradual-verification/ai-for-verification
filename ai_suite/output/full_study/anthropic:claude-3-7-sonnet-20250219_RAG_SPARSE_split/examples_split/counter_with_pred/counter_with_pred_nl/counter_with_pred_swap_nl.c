#include "stdlib.h"

struct Counter {
  int value;
};

/*@
// Define a predicate for the Counter struct
predicate counter(struct Counter* c, int v) =
    c->value |-> v &*& malloc_block_Counter(c);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The swap function swaps the values of the two Counters.

@param c1, c2: pointers to two Counter

The function makes sure that the two counters have their values swapped.
*/
void swap(struct Counter* c1, struct Counter* c2)
//@ requires counter(c1, ?v1) &*& counter(c2, ?v2);
//@ ensures counter(c1, v2) &*& counter(c2, v1);
{
  //@ open counter(c1, v1);
  //@ open counter(c2, v2);
  
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  
  //@ close counter(c1, v2);
  //@ close counter(c2, v1);
}