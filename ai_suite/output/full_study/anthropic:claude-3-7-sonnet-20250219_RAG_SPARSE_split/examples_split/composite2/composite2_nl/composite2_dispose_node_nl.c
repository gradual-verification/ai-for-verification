#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a recursive predicate for the binary tree structure
predicate tree(struct node *node) =
    node == 0 ?
        true
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> ?parent &*&
        node->count |-> ?count &*&
        malloc_block_node(node) &*&
        tree(left) &*&
        tree(right);
@*/

// TODO: make this function pass the verification
/*`dispose_node()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function frees the memory allocated for the node and its subtree

It makes sure that the subtree of the node is freed. */
void dispose_node(struct node *node)
//@ requires tree(node);
//@ ensures true;
{
    if (node == 0) {
        //@ open tree(node);
    } else {
        //@ open tree(node);
        {
            struct node *left = node->left;
            //@ assert tree(left);
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            //@ assert tree(right);
            dispose_node(right);
        }
        free(node);
    }
}