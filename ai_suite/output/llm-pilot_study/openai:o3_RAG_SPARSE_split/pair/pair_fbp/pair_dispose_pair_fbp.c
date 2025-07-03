#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    malloc_block_pair(p) &*&
    p->x |-> x &*&
    p->y |-> y;
@*/

// verified deallocation function
void dispose_pair(struct pair *p)
    //@ requires pair(p, _, _);
    //@ ensures  true;
{
    //@ open pair(p, _, _);   // expose the malloc block and the fields
    //@ open_struct(p);       // turn the field chunks into a chars_ chunk
    free(p);                 // free needs malloc_block + chars_
}