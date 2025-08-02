#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a node in the tree
predicate node_struct(struct node *n) =
    n == 0 ?
        emp
    :
        n->left |-> ?left &*&
        n->right |-> ?right &*&
        n->parent |-> ?parent &*&
        n->count |-> ?count &*&
        malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*`tree_has_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a right child 

It makes sure that the tree is not changed. */
bool tree_has_right(struct node *node)
    //@ requires node_struct(node);
    //@ ensures node_struct(node) &*& result == (node != 0 && node->right != 0);
{
    bool result = false;
    if (node == 0) {
        //@ open node_struct(node);
    } else {
        //@ open node_struct(node);
        struct node *right = node->right;
        result = right != 0;
        //@ close node_struct(node);
    }
    return result;
}