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

// verified version
struct pair* copy_pair(struct pair *p)
    //@ requires pair(p, ?x, ?y);
    //@ ensures  pair(p,  x, y) &*&
    //@          pair(result, x, y);
{
    /* Read the current contents of the original pair.
       We must open the predicate to gain field-access
       permissions, and re-close it afterwards. */
    //@ open pair(p, x, y);
    int tmp_x = p->x;
    int tmp_y = p->y;
    //@ close pair(p, x, y);

    /* Allocate and initialise the copy. */
    struct pair *new_p = malloc(sizeof(struct pair));
    if (new_p == 0) abort();
    new_p->x = tmp_x;
    new_p->y = tmp_y;

    /* The values we stored are the same as the ones read
       from the original pair. */
    //@ assert tmp_x == x &*& tmp_y == y;

    /* Finish the proof for the newly created pair. */
    //@ close pair(new_p, x, y);
    return new_p;
}