#include "stdlib.h"

/*@
predicate tree_node(struct node *n) =
    n != 0 &*&
    n->left |-> ?left &*&
    n->right |-> ?right &*&
    n->parent |-> ?parent &*&
    n->count |-> ?count &*&
    malloc_block_node(n);
@*/

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

// TODO: make this function pass the verification
/*tree_has_right function
-param: struct node *node
-description: The function checks if the right node of the
current node is not null. It requires that before the call, the current node is non-null.

It makes sure that the tree is unchanged and the returned value is true if the right child is not null.
*/
bool tree_has_right(struct node *node)
    //@ requires tree_node(node);
    //@ ensures tree_node(node) &*& result == (node->right != 0);
{
    //@ open tree_node(node);
    struct node *right = node->right;
    //@ close tree_node(node);
    return right != 0;
}