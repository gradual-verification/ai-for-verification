#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate subtree(struct node *n, struct node *p) =
    n == 0 ?
        true
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> _ &*&
        malloc_block_node(n) &*&
        subtree(l, n) &*&
        subtree(r, n);

predicate tree(struct node *n) = subtree(n, 0);
@*/


/*dispose_node function
-param: struct node *node
-description: The function disposes the tree by calling
itself recursively on the left and right nodes of the
current node. It then frees the current node.

It makes sure that the subtree of node is freed.
*/
void dispose_node(struct node *node)
    //@ requires subtree(node, _);
    //@ ensures true;
{
    if (node == 0) {
        //@ open subtree(node, _);
    } else {
        //@ open subtree(node, _);
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
    //@ requires tree(node);
    //@ ensures true;
{
    //@ open tree(node);
    dispose_node(node);
}