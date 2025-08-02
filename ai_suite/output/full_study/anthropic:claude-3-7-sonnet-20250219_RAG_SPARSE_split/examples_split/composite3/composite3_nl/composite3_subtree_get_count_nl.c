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
        tree_node(left, ?leftCount) &*&
        tree_node(right, ?rightCount) &*&
        count == 1 + leftCount + rightCount;
@*/

// TODO: make this function pass the verification
/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
//@ requires tree_node(node, ?count);
//@ ensures tree_node(node, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
        //@ close tree_node(node, 0);
    } else {
        //@ open tree_node(node, count);
        result = node->count;
        //@ close tree_node(node, count);
    }
    return result;
}