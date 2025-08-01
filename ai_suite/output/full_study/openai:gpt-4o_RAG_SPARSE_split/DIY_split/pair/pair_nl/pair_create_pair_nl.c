#include "stdlib.h"

struct pair {
    int x;
    int y;
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_pair` function creates a pair with the given values.
 *
 * @param x, y: the values in the new pair
 *
 * The function makes sure that the returned pair has its x and y set. 
 */
/*@ 
predicate pair(struct pair *p; int x, int y) =
    p->x |-> x &*& p->y |-> y &*& malloc_block_pair(p);
@*/

struct pair* create_pair(int x, int y)
    //@ requires true;
    //@ ensures result == 0 ? true : pair(result, x, y);
{
    struct pair* p = malloc(sizeof(struct pair));
    if (p == 0) abort();
    p->x = x;
    p->y = y;
    //@ close pair(p, x, y);
    return p;
}