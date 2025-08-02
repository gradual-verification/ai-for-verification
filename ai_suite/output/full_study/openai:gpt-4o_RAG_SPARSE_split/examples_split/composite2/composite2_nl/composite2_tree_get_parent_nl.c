#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n; struct node *parent) =
    n == 0 ?
        parent == 0
    :
        n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> parent &*& n->count |-> _ &*&
        malloc_block_node(n) &*&
        node(left, n) &*& node(right, n);

@*/

// TODO: make this function pass the verification
/*tree_get_parent Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the parent node 

It makes sure to return the parent node in the tree. */
struct node *tree_get_parent(struct node *node)
    //@ requires node(node, ?parent);
    //@ ensures node(node, parent) &*& result == parent;
{
    if (node == 0) {
        abort();
    }
    {
        struct node *parent = node->parent;
        if (parent == 0) {
            abort();
        }
        return parent;
    }
}