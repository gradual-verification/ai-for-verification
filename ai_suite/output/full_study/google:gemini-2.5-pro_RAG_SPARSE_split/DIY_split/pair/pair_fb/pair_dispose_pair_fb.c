#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
// To allow freeing the struct, the predicate must also own the memory block.
// malloc_block_pair(p) represents ownership of the memory allocated for a 'struct pair'.
predicate pair(struct pair *p, int x, int y) =
    p->x |-> x &*& p->y |-> y &*& malloc_block_pair(p);
@*/

void dispose_pair(struct pair *p)
    //@ requires pair(p, _, _);
    //@ ensures true;
{
    //@ open pair(p, _, _);
    free(p);
}