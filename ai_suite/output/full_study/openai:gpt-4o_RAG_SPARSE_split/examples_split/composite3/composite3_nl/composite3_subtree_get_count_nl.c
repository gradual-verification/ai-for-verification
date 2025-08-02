#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate tree(struct node *n) =
    n == 0 ? true : n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*& n->count |-> ?count &*&
    malloc_block_node(n) &*& tree(left) &*& tree(right);

@*/

// TODO: make this function pass the verification
/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(node) &*& result == (node == 0 ? 0 : node->count);
{
    int result = 0;
    if (node == 0) {
        result = 0;
    } else {
        result = node->count;
    }
    return result;
}