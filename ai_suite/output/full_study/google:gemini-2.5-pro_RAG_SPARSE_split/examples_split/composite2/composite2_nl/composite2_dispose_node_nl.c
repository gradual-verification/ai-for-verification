#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate tree(struct node *n;) =
    n == 0 ?
        true
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> ?p &*&
        n->count |-> ?c &*&
        malloc_block_node(n) &*&
        tree(l) &*&
        tree(r);
@*/

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
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        free(node);
    }
}