#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a tree node
predicate tree_node(struct node *node) =
    node == 0 ?
        emp
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> ?parent &*&
        node->count |-> ?count &*&
        malloc_block_node(node);
@*/

// TODO: make this function pass the verification
/*`tree_has_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a left child

It makes sure that the tree is not changed. */
bool tree_has_left(struct node *node)
//@ requires tree_node(node);
//@ ensures tree_node(node) &*& result == (node != 0 && node->left != 0);
{
    bool result = false;
    if (node == 0) {
        //@ close tree_node(node);
    } else {
        //@ open tree_node(node);
        struct node *left = node->left;
        result = left != 0;
        //@ close tree_node(node);
    }
    return result;
}