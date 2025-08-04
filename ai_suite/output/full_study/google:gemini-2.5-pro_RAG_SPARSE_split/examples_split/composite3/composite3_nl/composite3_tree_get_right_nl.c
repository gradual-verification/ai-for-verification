#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// A predicate to represent ownership of a single, non-null node.
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n != 0 &*&
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*tree_get_right function
-param: struct node *node
-description: The function gets the right node of the
current node. It requires that before the call, the current node and its right child are non-null.
It makes sure that the returned value is the right child of the current node and the tree is not changed.
*/
struct node *tree_get_right(struct node *node)
    //@ requires node(node, ?l, ?r, ?p, ?c) &*& r != 0;
    //@ ensures node(node, l, r, p, c) &*& result == r;
{
    //@ open node(node, l, r, p, c);
    struct node *right = node->right;
    //@ close node(node, l, r, p, c);
    return right;
}