#include "stdlib.h"

// Define the predicate for the counter structure
/*@
predicate counter_f(struct counter *c, int v) =
    c->f |-> v &*& malloc_block_counter(c);
@*/

// Define the function m with the required specifications
void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v);
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}