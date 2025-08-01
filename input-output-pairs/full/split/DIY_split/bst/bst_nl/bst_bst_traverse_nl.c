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
 * The `bst_traverse` function traverses the subtree of a given node.
 *
 * @param node: the node to be traversed on, which is a root of a bst
 *
 * The function makes sure that the given node is still a root of a bst. 
 */
void bst_traverse(struct bst_node *node)
{
    if (node == 0) {
    } else {
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
    }
}
