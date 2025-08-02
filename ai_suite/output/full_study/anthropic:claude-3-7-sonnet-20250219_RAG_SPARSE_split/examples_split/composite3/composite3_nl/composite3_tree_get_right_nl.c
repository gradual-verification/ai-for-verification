#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a node in the tree
predicate node_with_right(struct node *node, struct node *right) =
    node != 0 &*&
    node->right |-> right &*&
    right != 0;
@*/

// TODO: make this function pass the verification
/*tree_get_right function
-param: struct node *node
-description: The function gets the right node of the
current node. It requires that before the call, the current node and its right child are non-null.
It makes sure that the returned value is the right child of the current node and the tree is not changed.
*/
struct node *tree_get_right(struct node *node)
//@ requires node_with_right(node, ?right);
//@ ensures node_with_right(node, right) &*& result == right;
{
    //@ open node_with_right(node, right);
    struct node *right = node->right;
    //@ close node_with_right(node, right);
    return right;
}