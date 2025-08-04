#include "stdlib.h"

struct Counter {
  int value;
};

/*@
// Predicate to describe the memory layout and ownership of a Counter struct.
// It states that 'c' points to a Counter struct whose 'value' field is 'v'.
predicate Counter_p(struct Counter* c; int v) =
    c->value |-> v &*&
    malloc_block_Counter(c);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The increment function increments the value of the counter by 1.

@param c: a pointer to a Counter

The function makes sure that the counter has its value incremented by 1.
*/
void increment(struct Counter* c)
    //@ requires Counter_p(c, ?v) &*& v < INT_MAX;
    //@ ensures Counter_p(c, v + 1);
{
  int tmp = c->value;
  c->value = tmp + 1;
}