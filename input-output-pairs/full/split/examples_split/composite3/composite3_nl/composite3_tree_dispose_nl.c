#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



/*dispose_node function
-param: struct node *node
-description: The function disposes the tree by calling
itself recursively on the left and right nodes of the
current node. It then frees the current node.

It makes sure that the subtree of node is freed.
*/
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
/*tree_dispose function
-param: struct node *node
-description: The function disposes the tree by calling 
the dispose_node function.

It makes sure that the tree of noed is freed.
*/
void tree_dispose(struct node *node)
{
    dispose_node(node);
}

