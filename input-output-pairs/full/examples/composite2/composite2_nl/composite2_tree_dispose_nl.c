#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



/*`dispose_node()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function frees the memory allocated for the node and its subtree

It makes sure that the subtree of the node is freed. */
void dispose_node(struct node *node)
{
    if (node == 0) {
    } else {
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        free(node);
    }
}

// TODO: make this function pass the verification
/*`tree_dispose()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function disposes of the tree

It makes sure that the tree is freed. */
void tree_dispose(struct node *node)
{
    if (node == 0) {
        abort();
    }
    {
        struct node *parent = node->parent;
        if (parent != 0) {
            abort();
        }
    }
    dispose_node(node);
}

