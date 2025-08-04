#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    malloc_block_pair(p) &*& p->x |-> x &*& p->y |-> y;
@*/

// This function is verified by VeriFast without any changes to its body.
// VeriFast automatically opens the `pair` predicate to verify the field
// assignments and automatically closes it at the end of the function to
// satisfy the postcondition.
void update_pair(struct pair *p, int new_x, int new_y)
    //@ requires pair(p, _, _);
    //@ ensures pair(p, new_x, new_y);
{
    p->x = new_x;
    p->y = new_y;
}