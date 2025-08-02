#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n;) =
    n == 0 ? emp : 
    n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*& n->count |-> _ &*&
    malloc_block_node(n) &*& node(left) &*& node(right);

@*/

/*dispose_node function
-param: struct node *node
-description: The function disposes the tree by calling
itself recursively on the left and right nodes of the
current node. It then frees the current node.

It makes sure that the subtree of node is freed.
*/
void dispose_node(struct node *node)
    //@ requires node(node);
    //@ ensures emp;
{
    if (node == 0) {
        //@ open node(node);
    } else {
        //@ open node(node);
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

It makes sure that the tree of node is freed.
*/
void tree_dispose(struct node *node)
    //@ requires node(node);
    //@ ensures emp;
{
    dispose_node(node);
}