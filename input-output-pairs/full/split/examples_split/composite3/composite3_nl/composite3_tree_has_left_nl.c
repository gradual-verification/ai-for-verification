#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



// TODO: make this function pass the verification
/*tree_has_left function
-param: struct node *node
-description: The function checks if the left node of the
current node is not null. It requires that before the call, the current node is non-null.

It makes sure that the tree is unchanged and the returned value is true if the left child is not null.
*/
bool tree_has_left(struct node *node)
{
    struct node *left = node->left;
    return left != 0;
}

