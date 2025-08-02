#include "stdlib.h"
#include "stdbool.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n; struct node *parent) =
    n == 0 ?
        true
    :
        n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> parent &*& n->count |-> _ &*&
        malloc_block_node(n) &*&
        node(left, n) &*& node(right, n);

@*/

// TODO: make this function pass the verification
/*`tree_has_parent()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a parent

It makes sure that the tree is not changed. */
bool tree_has_parent(struct node *node)
    //@ requires node(node, ?parent);
    //@ ensures node(node, parent) &*& result == (parent != 0);
{
    bool result = false;
    if (node == 0) {
        result = false;
    } else {
        struct node *parent = node->parent;
        result = parent != 0;
    }
    return result;
}