#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



// TODO: make this function pass the verification
/*`tree_has_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a right child 

It makes sure that the tree is not changed. */
bool tree_has_right(struct node *node)
{
    bool result = false;
    if (node == 0) {
    } else {
        struct node *right = node->right;
        result = right != 0;
    }
    return result;
}

