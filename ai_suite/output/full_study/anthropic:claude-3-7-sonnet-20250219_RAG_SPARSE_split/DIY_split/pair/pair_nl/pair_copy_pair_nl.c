#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
// Define a predicate for the pair structure
predicate pair_pred(struct pair *p; int x, int y) =
    p->x |-> x &*& p->y |-> y &*& malloc_block_pair(p);
@*/

/***
 * Description:
 * The `copy_pair` function copies the given pair into the return value.
 *
 * @param p: the given pair to be copied
 *
 * It makes sure that p is not changed, and the returned pair has the same values as p. 
 */
struct pair* copy_pair(struct pair *p)
    //@ requires pair_pred(p, ?x, ?y);
    //@ ensures pair_pred(p, x, y) &*& pair_pred(result, x, y);
{
    //@ open pair_pred(p, x, y);
    struct pair* new_p = malloc(sizeof(struct pair));
    if (new_p == 0) abort();
    new_p->x = p->x;
    new_p->y = p->y;
    //@ close pair_pred(p, x, y);
    //@ close pair_pred(new_p, x, y);
    return new_p;
}