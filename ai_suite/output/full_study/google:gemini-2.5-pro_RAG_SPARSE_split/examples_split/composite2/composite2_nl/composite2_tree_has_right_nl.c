#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// This predicate describes the memory layout of a single, non-null `node`.
// `n` is an input parameter; `l`, `r`, `p`, and `c` are output parameters.
// This makes the predicate "precise", allowing VeriFast to merge fractional chunks.
predicate node_pred(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
    n->left |-> l &*&
    n->right |-> r &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*`tree_has_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a right child 

It makes sure that the tree is not changed. */
bool tree_has_right(struct node *node)
    //@ requires node == 0 ? emp : [?f]node_pred(node, ?l, ?r, ?p, ?c);
    //@ ensures node == 0 ? emp : [f]node_pred(node, l, r, p, c) &*& result == (node != 0 && r != 0);
{
    bool result = false;
    if (node == 0) {
        // If node is null, result remains false.
        // The postcondition holds: emp is returned, and `result` is false,
        // which matches `(0 != 0 && r != 0)`.
    } else {
        // If node is not null, we have permission to access its fields.
        //@ open [f]node_pred(node, l, r, p, c);
        struct node *right = node->right;
        result = right != 0;
        //@ close [f]node_pred(node, l, r, p, c);
        // The postcondition holds: the predicate is restored, and `result` is `(r != 0)`,
        // which matches `(node != 0 && r != 0)` since `node` is not null here.
    }
    return result;
}