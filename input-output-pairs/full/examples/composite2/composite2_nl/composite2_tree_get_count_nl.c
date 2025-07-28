#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
{
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}


// TODO: make this function pass the verification
/*`tree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function is used to get the 
count value of the tree starting from the given node.

This function makes sure that the tree of node is not changed. */
int tree_get_count(struct node *node)
{
    int result = subtree_get_count(node);
    return result;
}

