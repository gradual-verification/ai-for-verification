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
    //@ requires node(node);
    //@ ensures node(node) &*& result == (node->left != 0);
{
    //@ open node(node);
    struct node *left = node->left;
    //@ close node(node);
    return left != 0;
}