#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



// TODO: make this function pass the verification
/*`tree_get_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the left child node 

It makes sure to return the left node in the tree. */
struct node *tree_get_left(struct node *node)
{
    if (node == 0) {
        abort();
    }
    {
        struct node *left = node->left;
        return left;
    }
}

