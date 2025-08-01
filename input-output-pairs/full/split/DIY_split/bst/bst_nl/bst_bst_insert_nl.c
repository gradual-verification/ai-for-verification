#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `bst_insert` function inserts a value into the BST.
 *
 * @param node: the root of the BST
 * @param value: the value to be inserted
 * 
 * The function requires that the value is within the range of possible MAX and MIN value of BST,
 * and ensures that the returned node is still a root of a BST.
 */
struct bst_node *bst_insert(struct bst_node *node, int value)
{
    if (node == 0) {
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        return new_node;
    } else {
        if (value < node->value) {
            node->left = bst_insert(node->left, value);
        } else if (value > node->value) {
            node->right = bst_insert(node->right, value);
        } else {   
        }

        return node;
    }
}
