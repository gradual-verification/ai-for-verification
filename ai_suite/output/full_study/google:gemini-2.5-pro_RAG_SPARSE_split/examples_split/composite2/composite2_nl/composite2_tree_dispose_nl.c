#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// A predicate representing a node and its descendants.
// 'n' is the root of the subtree, and 'p' is its parent.
predicate subtree(struct node *n, struct node *p) =
    n == 0 ?
        emp
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> _ &*&
        malloc_block_node(n) &*&
        subtree(l, n) &*&
        subtree(r, n);

// A predicate for a full tree, where the root's parent is NULL.
predicate is_tree(struct node *n) = subtree(n, 0);
@*/


/*`dispose_node()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function frees the memory allocated for the node and its subtree

It makes sure that the subtree of the node is freed. */
void dispose_node(struct node *node)
    //@ requires subtree(node, _);
    //@ ensures emp;
{
    if (node == 0) {
        //@ open subtree(0, _);
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

/*`tree_dispose()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function disposes of the tree

It makes sure that the tree is freed. */
void tree_dispose(struct node *node)
    //@ requires is_tree(node) &*& node != 0;
    //@ ensures emp;
{
    if (node == 0) {
        abort();
    }
    //@ open is_tree(node);
    {
        struct node *parent = node->parent;
        if (parent != 0) {
            abort();
        }
    }
    //@ close subtree(node, 0);
    dispose_node(node);
}