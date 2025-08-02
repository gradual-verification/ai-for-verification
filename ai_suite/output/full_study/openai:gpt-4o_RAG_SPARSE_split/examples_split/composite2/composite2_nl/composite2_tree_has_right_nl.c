#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n;) =
    n == 0 ? true : n->left |-> _ &*& n->right |-> _ &*& n->parent |-> _ &*& n->count |-> _ &*& malloc_block_node(n);

@*/

// TODO: make this function pass the verification
/*`tree_has_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a right child 

It makes sure that the tree is not changed. */
bool tree_has_right(struct node *node)
    //@ requires node(node);
    //@ ensures node(node) &*& result == (node != 0 && node->right != 0);
{
    bool result = false;
    if (node == 0) {
        //@ open node(node);
    } else {
        //@ open node(node);
        struct node *right = node->right;
        result = right != 0;
        //@ close node(node);
    }
    return result;
}