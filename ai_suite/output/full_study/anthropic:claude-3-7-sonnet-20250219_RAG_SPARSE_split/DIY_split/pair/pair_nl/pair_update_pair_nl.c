#include "stdlib.h"

struct pair {
    int x;
    int y;
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `update_pair` function updates the values of a given pair with the given values.
 *
 * @param p: the given pair to be updated
 * @param new_x, new_y: the values in the new pair
 *
 * It makes sure that p has its x and y values updated by new_x and new_y. 
 */
/*@
    // Predicate to represent a valid pair structure
    predicate pair_struct(struct pair *p, int x, int y) =
        p->x |-> x &*& p->y |-> y &*& malloc_block_pair(p);
@*/

void update_pair(struct pair *p, int new_x, int new_y)
    //@ requires pair_struct(p, ?old_x, ?old_y);
    //@ ensures pair_struct(p, new_x, new_y);
{
    p->x = new_x;
    p->y = new_y;
}