#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node_pred(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n != 0 &*&
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_node(n);

@*/

/*tree_has_right function
-param: struct node *node
-description: The function checks if the right node of the
current node is not null. It requires that before the call, the current node is non-null.

It makes sure that the tree is unchanged and the returned value is true if the right child is not null.
*/
bool tree_has_right(struct node *node)
    //@ requires [?f]node_pred(node, ?l, ?r, ?p, ?c);
    //@ ensures [f]node_pred(node, l, r, p, c) &*& result == (r != 0);
{
    //@ open [f]node_pred(node, l, r, p, c);
    struct node *right = node->right;
    //@ close [f]node_pred(node, l, r, p, c);
    return right != 0;
}