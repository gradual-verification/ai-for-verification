#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
// Define malloc_block_pair predicate for struct pair
predicate malloc_block_pair(struct pair *p) = malloc_block(p, sizeof(struct pair));

predicate pair(struct pair *p, int x, int y) =
    malloc_block_pair(p) &*& p->x |-> x &*& p->y |-> y;
@*/

// Verified implementation of update_pair
void update_pair(struct pair *p, int new_x, int new_y)
    //@ requires pair(p, _, _);
    //@ ensures pair(p, new_x, new_y);
{
    //@ open pair(p, _, _);  // Unfold predicate to access fields
    p->x = new_x;          // Update x field
    p->y = new_y;          // Update y field
    //@ close pair(p, new_x, new_y);  // Refold predicate with new values
}