#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The nested_blocks function tests whether the goto statement can get out of the while loop,
and it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function

It makes sure that nodes n1 and n2 are not modified.
*/
void nested_blocks(struct node *n1, struct node *n2)
{
    while (true)
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
}

