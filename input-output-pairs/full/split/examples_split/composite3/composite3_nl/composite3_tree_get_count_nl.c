#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
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
/*tree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the tree is unchanged and the returned value is the count of the tree.
*/
int tree_get_count(struct node *node)
{
    int result = subtree_get_count(node);
    return result;
}

