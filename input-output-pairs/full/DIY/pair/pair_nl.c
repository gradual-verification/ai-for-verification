#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/***
 * Description:
 * The `create_pair` function creates a pair with the given values.
 *
 * @param x, y: the values in the new pair
 *
 * The function allocates memory for a new `pair` and sets its values, 
 * It makes sure that the new pair has the structure of pair. 
 */
struct pair* create_pair(int x, int y)
{
    struct pair* p = malloc(sizeof(struct pair));
    if (p == 0) abort();
    p->x = x;
    p->y = y;
    return p;
}

/***
 * Description:
 * The `update_pair` function updates the values of a given pair with the given values.
 *
 * @param p: the given pair to be updated, which has the structure of pair
 * @param x, y: the values in the new pair
 *
 * It makes sure that the new pair has the structure of pair and the values are updated. 
 */
void update_pair(struct pair *p, int new_x, int new_y)
{
    p->x = new_x;
    p->y = new_y;
}

/***
 * Description:
 * The `copy_pair` function copies the given pair into the return value.
 *
 * @param p: the given pair to be copied, which has the structure of pair
 *
 * It makes sure that the returned pair has the structure of pair and the same value as the given pair. 
 */
struct pair* copy_pair(struct pair *p)
{
    struct pair* new_p = malloc(sizeof(struct pair));
    if (new_p == 0) abort();
    new_p->x = p->x;
    new_p->y = p->y;
    return new_p;
}

/***
 * Description:
 * The `dispose_pair` function disposes the given pair by freeing it
 *
 * @param p: the given pair to be disposed, which has the structure of pair
 *
 * It makes sure that the given pair is freed. 
 */
void dispose_pair(struct pair *p)
{
    free(p);
}


/***
 * Description:
 * The `main` function tests the operations of pair.
 */
int main()
{
    struct pair* p = create_pair(1, 2);
    update_pair(p, 3, 4);
    
    struct pair* p_copy = copy_pair(p);
    
    dispose_pair(p);
    dispose_pair(p_copy);
    
    return 0;
}
