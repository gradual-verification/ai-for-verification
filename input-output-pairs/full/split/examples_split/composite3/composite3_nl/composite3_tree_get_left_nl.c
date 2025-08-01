#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



// TODO: make this function pass the verification
/*tree_get_left function
-param: struct node *node
-description: The function gets the left node of the
current node. It requires that before the call, the current node and its left child are non-null.
It makes sure that the returned value is the left child of the current node and the tree is not changed.
*/
struct node *tree_get_left(struct node *node)
{
    struct node *left = node->left;
    return left;
}

