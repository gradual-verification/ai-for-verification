#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Predicate for a single node in the tree.
// It represents ownership of the node's fields and its memory block.
predicate node(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
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
    //@ requires [?f]node(node, ?l, ?r, ?p, ?c);
    //@ ensures [f]node(node, l, r, p, c) &*& result == (l != 0);
{
    //@ open [f]node(node, l, r, p, c);
    struct node *left = node->left;
    //@ close [f]node(node, l, r, p, c);
    return left != 0;
}