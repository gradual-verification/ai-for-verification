#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a recursive predicate for a tree node
predicate tree_node(struct node *node) =
    node == 0 ?
        true
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> ?parent &*&
        node->count |-> ?count &*&
        malloc_block_node(node) &*&
        tree_node(left) &*&
        tree_node(right);
@*/

/*dispose_node function
-param: struct node *node
-description: The function disposes the tree by calling
itself recursively on the left and right nodes of the
current node. It then frees the current node.

It makes sure that the subtree of node is freed.
*/
void dispose_node(struct node *node)
//@ requires tree_node(node);
//@ ensures true;
{
    if (node == 0) {
        //@ open tree_node(node);
    } else {
        //@ open tree_node(node);
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        free(node);
    }
}


// TODO: make this function pass the verification
/*tree_dispose function
-param: struct node *node
-description: The function disposes the tree by calling 
the dispose_node function.

It makes sure that the tree of noed is freed.
*/
void tree_dispose(struct node *node)
//@ requires tree_node(node);
//@ ensures true;
{
    dispose_node(node);
}