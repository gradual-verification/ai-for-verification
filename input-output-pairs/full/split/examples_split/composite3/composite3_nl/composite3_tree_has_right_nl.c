#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



// TODO: make this function pass the verification
/*tree_has_right function
-param: struct node *node
-description: The function checks if the right node of the
current node is not null. It requires that before the call, the current node is non-null.

It makes sure that the tree is unchanged and the returned value is true if the right child is not null.
*/
bool tree_has_right(struct node *node)
{
    struct node *right = node->right;
    return right != 0;
}

