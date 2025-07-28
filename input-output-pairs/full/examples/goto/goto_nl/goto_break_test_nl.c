#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The break_test function tests whether the break statement can get out of the while loop,
and it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function

It makes sure that n1 and n2 are unchanged. 
*/
void break_test(struct node *n1, struct node *n2)
{
    while (true)
    {
        break;
    }
}
