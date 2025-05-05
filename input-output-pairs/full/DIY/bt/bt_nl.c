#include "stdlib.h"

// a binary tree node
struct tree_node {
    struct tree_node *left;
    struct tree_node *right;
    int value;
};

/***
 * Description:
 * The `tree_create_leaf` function creates a leaf node with the given value.
 *
 * @param val: the value in the new leaf node
 *
 * The function makes sure that the new node is the root of a tree. 
 */
struct tree_node *tree_create_leaf(int val)
{
    struct tree_node *node = malloc(sizeof(struct tree_node));
    if (node == 0) abort();
    node->value = val;
    node->left = 0;
    node->right = 0;
    return node;
}

/***
 * Description:
 * The `tree_create_node` function creates a node with the given value, left child and right child.
 *
 * @param val: the value in the new node
 * @param left: the node as the left child, which is a root of a tree
 * @param right: the node as the right child, which is a root of a tree
 *
 * The function makes sure that the new node is a root of a tree. 
 */
struct tree_node *tree_create_node(int val, struct tree_node *left, struct tree_node *right)
{
    struct tree_node *node = malloc(sizeof(struct tree_node));
    if (node == 0) abort();
    node->value = val;
    node->left = left;
    node->right = right;
    return node;
}

/***
 * Description:
 * The `tree_traverse` function traverses a given node.
 *
 * @param node: the node to be traversed on, which is a root of a tree
 *
 * The function makes sure that the given node is still a root of a tree. 
 */
void tree_traverse(struct tree_node *node)
{
    if (node == 0) {
    } else {
        int val = node->value;
        tree_traverse(node->left);
        tree_traverse(node->right);
    }
}

/***
 * Description:
 * The `tree_dispose` function disposes the tree rooted at a given node.
 *
 * @param node: the node as the root of a tree
 *
 * The function makes sure that the nodes in the tree are freed. 
 */
void tree_dispose(struct tree_node *node)
{
    if (node != 0) {
        tree_dispose(node->left);
        tree_dispose(node->right);
        free(node);
    }
}