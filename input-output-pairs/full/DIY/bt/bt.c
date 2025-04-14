#include "stdlib.h"

struct tree_node {
    struct tree_node *left;
    struct tree_node *right;
    int value;
};

/*@ 
predicate tree(struct tree_node *node) =
    node == 0 ?
        true
    :
        malloc_block_tree_node(node) &*&
        node->value |-> ?v &*&
        node->left |-> ?left &*& node->right |-> ?right &*&
        tree(left) &*& tree(right);
@*/

// Create a leaf node (no children)
struct tree_node *tree_create_leaf(int val)
    //@ requires emp;
    //@ ensures tree(result);
{
    struct tree_node *node = malloc(sizeof(struct tree_node));
    if (node == 0) abort();
    node->value = val;
    node->left = 0;
    node->right = 0;
    //@ close tree(0);
    //@ close tree(0);
    //@ close tree(node);
    return node;
}

// Create an internal node with given left and right subtrees
struct tree_node *tree_create_node(int val, struct tree_node *left, struct tree_node *right)
    //@ requires tree(left) &*& tree(right);
    //@ ensures tree(result);
{
    struct tree_node *node = malloc(sizeof(struct tree_node));
    if (node == 0) abort();
    node->value = val;
    node->left = left;
    node->right = right;
    //@ close tree(node);
    return node;
}

// Compute sum of all nodes
void tree_traverse(struct tree_node *node)
    //@ requires tree(node);
    //@ ensures tree(node);
{
    if (node == 0) {
    } else {
        //@ open tree(node);
        tree_traverse(node->left);
        tree_traverse(node->right);
        //@ close tree(node);
    }
}

// Dispose tree safely
void tree_dispose(struct tree_node *node)
    //@ requires tree(node);
    //@ ensures true;
{
    //@ open tree(node);
    if (node != 0) {
        tree_dispose(node->left);
        tree_dispose(node->right);
        free(node);
    }
}