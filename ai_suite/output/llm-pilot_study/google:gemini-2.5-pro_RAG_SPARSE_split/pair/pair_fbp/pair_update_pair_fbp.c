#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    malloc_block_pair(p) &*& p->x |-> x &*& p->y |-> y;
@*/

// TODO: make this function pass the verification
void update_pair(struct pair *p, int new_x, int new_y)
    //@ requires pair(p, ?old_x, ?old_y);
    //@ ensures pair(p, new_x, new_y);
{
    //@ open pair(p, old_x, old_y);
    p->x = new_x;
    p->y = new_y;
    //@ close pair(p, new_x, new_y);
}