#include "stdlib.h"

struct pair {
    int x;
    int y;
};

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
{
    free(p);
}
