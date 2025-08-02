#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
// Define a predicate for the pair structure
predicate pair(struct pair *p; int x, int y) =
    p->x |-> x &*& p->y |-> y &*& malloc_block_pair(p);
@*/

/***
 * Description:
 * The `create_pair` function creates a pair with the given values.
 *
 * @param x, y: the values in the new pair
 *
 * The function makes sure that the returned pair has its x and y set. 
 */
struct pair* create_pair(int x, int y)
//@ requires true;
//@ ensures pair(result, x, y);
{
    struct pair* p = malloc(sizeof(struct pair));
    if (p == 0) abort();
    p->x = x;
    p->y = y;
    //@ close pair(p, x, y);
    return p;
}

/***
 * Description:
 * The `update_pair` function updates the values of a given pair with the given values.
 *
 * @param p: the given pair to be updated
 * @param new_x, new_y: the values in the new pair
 *
 * It makes sure that p has its x and y values updated by new_x and new_y. 
 */
void update_pair(struct pair *p, int new_x, int new_y)
//@ requires pair(p, _, _);
//@ ensures pair(p, new_x, new_y);
{
    //@ open pair(p, _, _);
    p->x = new_x;
    p->y = new_y;
    //@ close pair(p, new_x, new_y);
}

/***
 * Description:
 * The `copy_pair` function copies the given pair into the return value.
 *
 * @param p: the given pair to be copied
 *
 * It makes sure that p is not changed, and the returned pair has the same values as p. 
 */
struct pair* copy_pair(struct pair *p)
//@ requires pair(p, ?x, ?y);
//@ ensures pair(p, x, y) &*& pair(result, x, y);
{
    //@ open pair(p, x, y);
    struct pair* new_p = malloc(sizeof(struct pair));
    if (new_p == 0) abort();
    new_p->x = p->x;
    new_p->y = p->y;
    //@ close pair(p, x, y);
    //@ close pair(new_p, x, y);
    return new_p;
}

/***
 * Description:
 * The `dispose_pair` function disposes the given pair by freeing it.
 *
 * @param p: the given pair to be disposed
 *
 * It makes sure that the given pair p is freed. 
 */
void dispose_pair(struct pair *p)
//@ requires pair(p, _, _);
//@ ensures true;
{
    //@ open pair(p, _, _);
    free(p);
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of pair.
 */
int main()
//@ requires true;
//@ ensures true;
{
    struct pair* p = create_pair(1, 2);
    update_pair(p, 3, 4);
    
    struct pair* p_copy = copy_pair(p);
    
    dispose_pair(p);
    dispose_pair(p_copy);
    
    return 0;
}