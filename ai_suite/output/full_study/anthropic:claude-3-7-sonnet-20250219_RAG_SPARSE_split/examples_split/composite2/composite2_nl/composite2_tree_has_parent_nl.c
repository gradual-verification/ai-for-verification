#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for the node structure
predicate node(struct node *n; struct node *parent, int count) =
    n == 0 ?
        emp
    :
        n->left |-> ?left &*&
        n->right |-> ?right &*&
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
    //@ requires node(node, ?parent, ?count);
    //@ ensures node(node, parent, count) &*& result == (parent != 0);
{
    bool result = false;
    if (node == 0) {
        //@ close node(node, parent, count);
    } else {
        //@ open node(node, parent, count);
        struct node *parent = node->parent;
        result = parent != 0;
        //@ close node(node, parent, count);
    }
    return result;
}