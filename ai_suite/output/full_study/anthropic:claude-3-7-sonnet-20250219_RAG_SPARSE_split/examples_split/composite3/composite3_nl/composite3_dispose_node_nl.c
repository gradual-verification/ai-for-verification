#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a recursive predicate for the tree structure
predicate tree(struct node *node) =
    node == 0 ?
        emp
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
/*dispose_node function
-param: struct node *node
-description: The function disposes the tree by calling
itself recursively on the left and right nodes of the
current node. It then frees the current node.

It makes sure that the subtree of node is freed.
*/
/*@
// Specification for dispose_node
requires tree(node);
ensures emp;
@*/
void dispose_node(struct node *node)
{
    if (node == 0) {
        //@ open tree(node);
    } else {
        //@ open tree(node);
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