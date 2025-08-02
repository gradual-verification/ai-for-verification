#include "stdlib.h"

struct Counter {
  int value;
};

/*@
// Define a predicate for the Counter struct
predicate counter(struct Counter* c; int value) =
  c->value |-> value &*& malloc_block_Counter(c);
@*/

/***
 * Description:
The increment function increments the value of the counter by 1.

@param c: a pointer to a Counter

The function makes sure that the counter has its value incremented by 1.
*/
void increment(struct Counter* c)
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v + 1);
{
  //@ open counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close counter(c, v + 1);
}