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
void dispose_pair(struct pair *p)
    /*@
    requires pair(p, _, _);
    @*/
    /*@
    ensures true;
    @*/
{
    free(p);
}