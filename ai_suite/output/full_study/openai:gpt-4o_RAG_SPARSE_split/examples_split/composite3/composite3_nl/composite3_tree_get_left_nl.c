#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n;) =
    n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*& n->count |-> ?count &*&
    malloc_block_node(n) &*&
    (left == 0 ? true : node(left)) &*&
    (right == 0 ? true : node(right));

@*/

// TODO: make this function pass the verification
/*tree_get_left function
-param: struct node *node
-description: The function gets the left node of the
current node. It requires that before the call, the current node and its left child are non-null.
It makes sure that the returned value is the left child of the current node and the tree is not changed.
*/
struct node *tree_get_left(struct node *node)
    //@ requires node(node) &*& node->left |-> ?left &*& left != 0;
    //@ ensures node(node) &*& node->left |-> left &*& result == left;
{
    struct node *left = node->left;
    return left;
}