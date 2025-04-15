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
        node->value |-> ?v &*&
        node->left |-> ?left &*& node->right |-> ?right &*&
        tree(left) &*& tree(right);
@*/

struct tree_node *tree_create_leaf(int val)
    //@ requires true;
    //@ ensures tree(result);
{
    struct tree_node *node = malloc(sizeof(struct tree_node));
    if (node == 0) abort();
    node->value = val;
    node->left = 0;
    node->right = 0;
    return node;
}

struct tree_node *tree_create_node(int val, struct tree_node *left, struct tree_node *right)
    //@ requires tree(left) &*& tree(right);
    //@ ensures tree(result);
{
    struct tree_node *node = malloc(sizeof(struct tree_node));
    if (node == 0) abort();
    node->value = val;
    node->left = left;
    node->right = right;
    return node;
}

void tree_traverse(struct tree_node *node)
    //@ requires tree(node);
    //@ ensures tree(node);
{
    if (node == 0) {
    } else {
        int val = node->value;
        tree_traverse(node->left);
        tree_traverse(node->right);
    }
}

void tree_dispose(struct tree_node *node)
    //@ requires tree(node);
    //@ ensures true;
{
    if (node != 0) {
        tree_dispose(node->left);
        tree_dispose(node->right);
        free(node);
    }
}