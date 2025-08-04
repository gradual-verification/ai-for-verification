#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// A predicate representing a single, allocated `struct node`.
// This is a precise predicate, where `n` is the input parameter, and the
// remaining parameters are output parameters representing the node's fields.
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*`tree_has_parent()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a parent

It makes sure that the tree is not changed. */
bool tree_has_parent(struct node *node)
    //@ requires node == 0 ? true : [?f]node(node, ?l, ?r, ?p, ?c);
    //@ ensures node == 0 ? result == false : [f]node(node, l, r, p, c) &*& result == (p != 0);
{
    bool result = false;
    if (node == 0) {
        // If the node is NULL, it has no parent. `result` is already false.
    } else {
        // If the node is not NULL, we open its predicate to access the parent field.
        //@ open [f]node(node, l, r, p, c);
        struct node *parent = node->parent;
        result = parent != 0;
        // We close the predicate to restore the memory chunk for the caller.
        //@ close [f]node(node, l, r, p, c);
    }
    return result;
}