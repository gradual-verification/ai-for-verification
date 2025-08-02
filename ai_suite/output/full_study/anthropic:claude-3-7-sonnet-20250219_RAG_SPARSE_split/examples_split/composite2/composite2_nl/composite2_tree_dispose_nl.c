#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate node_tree(struct node *n) =
    n == 0 ?
        emp
    :
        n->left |-> ?left &*&
        n->right |-> ?right &*&
        n->parent |-> ?parent &*&
        n->count |-> ?count &*&
        malloc_block_node(n) &*&
        node_tree(left) &*&
        node_tree(right) &*&
        (left != 0 ? left->parent |-> n : emp) &*&
        (right != 0 ? right->parent |-> n : emp);

predicate root_node(struct node *n) =
    n != 0 &*&
    n->parent |-> 0 &*&
    node_tree(n);
@*/

/*`dispose_node()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function frees the memory allocated for the node and its subtree

It makes sure that the subtree of the node is freed. */
void dispose_node(struct node *node)
//@ requires node_tree(node);
//@ ensures emp;
{
    if (node == 0) {
        //@ close emp;
    } else {
        //@ open node_tree(node);
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
/*`tree_dispose()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function disposes of the tree

It makes sure that the tree is freed. */
void tree_dispose(struct node *node)
//@ requires root_node(node);
//@ ensures emp;
{
    if (node == 0) {
        abort();
    }
    {
        //@ open root_node(node);
        struct node *parent = node->parent;
        if (parent != 0) {
            abort();
        }
    }
    dispose_node(node);
}