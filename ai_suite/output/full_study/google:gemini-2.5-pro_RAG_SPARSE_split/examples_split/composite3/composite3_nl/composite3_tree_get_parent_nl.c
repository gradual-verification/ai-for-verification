#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate node(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
    n != 0 &*&
    n->left |-> l &*&
    n->right |-> r &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*tree_get_parent function
-param: struct node *node
-description: The function gets the parent of the
current node. It requires that before the call, the current node and its parent are non-null.
It makes sure that the returned value is the parent of the current node and the tree is not changed.
*/
struct node *tree_get_parent(struct node *node)
    //@ requires node(node, ?l, ?r, ?p, ?c) &*& p != 0;
    //@ ensures node(node, l, r, p, c) &*& result == p;
{
    //@ open node(node, l, r, p, c);
    struct node *parent = node->parent;
    //@ close node(node, l, r, p, c);
    return parent;
}