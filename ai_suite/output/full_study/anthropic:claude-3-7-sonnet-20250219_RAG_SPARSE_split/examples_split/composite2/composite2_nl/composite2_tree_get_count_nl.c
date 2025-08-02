#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Predicate to represent a valid tree node
predicate tree_node(struct node *node; int count) =
    node == 0 ?
        count == 0
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> ?parent &*&
        node->count |-> count &*&
        malloc_block_node(node) &*&
        tree_node(left, ?leftCount) &*&
        tree_node(right, ?rightCount) &*&
        count == leftCount + rightCount + 1;
@*/

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


// TODO: make this function pass the verification
/*`tree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function is used to get the 
count value of the tree starting from the given node.

This function makes sure that the tree of node is not changed. */
int tree_get_count(struct node *node)
//@ requires tree_node(node, ?count);
//@ ensures tree_node(node, count) &*& result == count;
{
    int result = subtree_get_count(node);
    return result;
}