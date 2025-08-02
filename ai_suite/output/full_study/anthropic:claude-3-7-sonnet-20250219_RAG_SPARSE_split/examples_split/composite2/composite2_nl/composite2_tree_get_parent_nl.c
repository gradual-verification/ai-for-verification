#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a node with a parent
predicate node_with_parent(struct node *n) =
    n != 0 &*&
    n->left |-> _ &*&
    n->right |-> _ &*&
    n->parent |-> ?p &*&
    n->count |-> _ &*&
    p != 0 &*&
    malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*tree_get_parent Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the parent node 

It makes sure to return the parent node in the tree. */
struct node *tree_get_parent(struct node *node)
//@ requires node_with_parent(node);
//@ ensures node_with_parent(old_node) &*& result == old_node->parent;
{
    //@ open node_with_parent(node);
    if (node == 0) {
        abort();
    }
    {
        struct node *parent = node->parent;
        if (parent == 0) {
            abort();
        }
        //@ close node_with_parent(node);
        return parent;
    }
}