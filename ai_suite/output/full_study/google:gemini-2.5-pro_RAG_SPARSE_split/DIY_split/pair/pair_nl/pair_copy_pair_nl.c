#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair_p(struct pair *p; int x, int y) =
    p->x |-> x &*&
    p->y |-> y &*&
    malloc_block_pair(p);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `copy_pair` function copies the given pair into the return value.
 *
 * @param p: the given pair to be copied
 *
 * It makes sure that p is not changed, and the returned pair has the same values as p. 
 */
struct pair* copy_pair(struct pair *p)
    //@ requires pair_p(p, ?x, ?y);
    //@ ensures pair_p(p, x, y) &*& pair_p(result, x, y) &*& result != p;
{
    struct pair* new_p = malloc(sizeof(struct pair));
    if (new_p == 0) abort();
    new_p->x = p->x;
    new_p->y = p->y;
    return new_p;
}