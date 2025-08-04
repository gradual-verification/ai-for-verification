#include "stdlib.h"

struct Counter {
  int value;
};

/*@
// Predicate representing ownership of a Counter struct.
predicate counter(struct Counter *c; int v) =
    c->value |-> v &*&
    malloc_block_Counter(c);
@*/

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
  //@ open counter(c, v);
  int tmp = c->value;
  //@ close counter(c, v);
  return tmp;
}