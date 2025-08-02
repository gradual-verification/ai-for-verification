#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a binary tree node
predicate tree_node(struct node *n; int count) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?left &*&
        n->right |-> ?right &*&
        n->parent |-> ?parent &*&
        n->count |-> count &*&
        malloc_block_node(n) &*&
        count > 0;
@*/

// TODO: make this function pass the verification
/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires tree_node(node, ?count);
    //@ ensures tree_node(node, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
        //@ open tree_node(node, count);
        //@ close tree_node(node, count);
    } else {
        //@ open tree_node(node, count);
        result = node->count;
        //@ close tree_node(node, count);
    }
    return result;
}