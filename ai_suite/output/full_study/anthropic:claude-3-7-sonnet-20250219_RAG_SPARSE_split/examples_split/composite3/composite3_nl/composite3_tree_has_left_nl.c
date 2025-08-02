#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for the node structure
predicate node_struct(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
    n->left |-> l &*&
    n->right |-> r &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*tree_has_left function
-param: struct node *node
-description: The function checks if the left node of the
current node is not null. It requires that before the call, the current node is non-null.

It makes sure that the tree is unchanged and the returned value is true if the left child is not null.
*/
bool tree_has_left(struct node *node)
    //@ requires node != 0 &*& node_struct(node, ?left, ?right, ?parent, ?count);
    //@ ensures node_struct(node, left, right, parent, count) &*& result == (left != 0);
{
    struct node *left = node->left;
    //@ open node_struct(node, left, right, parent, count);
    return left != 0;
    //@ close node_struct(node, left, right, parent, count);
}