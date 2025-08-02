#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a node in the tree
predicate node_with_parent(struct node *node, struct node *parent) =
    node != 0 &*&
    node->left |-> _ &*&
    node->right |-> _ &*&
    node->parent |-> parent &*&
    node->count |-> _ &*&
    malloc_block_node(node) &*&
    parent != 0;
@*/

// TODO: make this function pass the verification
/*tree_get_parent function
-param: struct node *node
-description: The function gets the parent of the
current node. It requires that before the call, the current node and its parent are non-null.
It makes sure that the returned value is the parent of the current node and the tree is not changed.
*/
struct node *tree_get_parent(struct node *node)
//@ requires node_with_parent(node, ?parent);
//@ ensures node_with_parent(node, parent) &*& result == parent;
{
    //@ open node_with_parent(node, parent);
    struct node *parent = node->parent;
    //@ close node_with_parent(node, parent);
    return parent;
}