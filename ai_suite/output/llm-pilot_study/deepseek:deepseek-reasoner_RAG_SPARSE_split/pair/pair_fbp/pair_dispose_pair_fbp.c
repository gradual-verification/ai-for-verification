#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    malloc_block_pair(p) &*& p->x |-> x &*& p->y |-> y;
@*/

void dispose_pair(struct pair *p)
    //@ requires pair(p, _, _);
    //@ ensures true;
{
    //@ open pair(p, _, _);
    // Convert the x field to a chars_ chunk
    //@ integer_to_chars((void *)&p->x);
    // Convert the y field to a chars_ chunk
    //@ integer_to_chars((void *)&p->y);
    // Combine the two chars_ chunks and the malloc_block into a single chars_ chunk for the entire struct
    //@ chars_join((void *)p);
    free(p);
}