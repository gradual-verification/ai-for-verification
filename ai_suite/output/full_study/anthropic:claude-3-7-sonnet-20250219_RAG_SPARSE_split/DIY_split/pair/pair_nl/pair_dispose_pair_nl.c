#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
// Define a predicate for the pair structure
predicate pair(struct pair *p) =
    p->x |-> _ &*& p->y |-> _ &*& malloc_block_pair(p);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_pair` function disposes the given pair by freeing it.
 *
 * @param p: the given pair to be disposed
 *
 * It makes sure that the given pair p is freed. 
 */
void dispose_pair(struct pair *p)
    //@ requires pair(p);
    //@ ensures emp;
{
    //@ open pair(p);
    free(p);
}