#include "stdlib.h"

struct Accumulator {
    int total;
    int count;
};

/*@
predicate malloc_block_Accumulator(struct Accumulator *a) = malloc_block(a, sizeof(struct Accumulator));

predicate Accumulator(struct Accumulator* a, int t, int c) =
    integer(&a->total, t) 
    &*& integer(&a->count, c)
    &*& malloc_block_Accumulator(a);
@*/

// Verified reset function
void reset(struct Accumulator* a)
    //@ requires Accumulator(a, _, _);
    //@ ensures Accumulator(a, 0, 0);
{
    a->total = 0;
    a->count = 0;
}