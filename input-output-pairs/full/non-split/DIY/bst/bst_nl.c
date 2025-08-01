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
 * The `bst_create` function creates an empty BST.
 *
 *
 * The function makes sure that the new node is the root of a BST. 
 */
struct bst_node *bst_create()
{
    return 0;
}

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

// TODO: make this function pass the verification
/***
 * Description:
 * The `bst_search` function searches a value in the given BST.
 *
 * @param node: the root of the BST
 * @param value: the value to be searched
 * 
 * The function makes sure that the BST is still valid after the search operation,
 */
bool bst_search(struct bst_node *node, int value)
{
    if (node == 0) {
        return false;
    }
    else if (node->value == value) {
        return true;
    }
    else if (value < node->value) {
        return bst_search(node->left, value);
    }
    else {
        return bst_search(node->right, value);
    }
}

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

// TODO: make this function pass the verification
/***
 * Description:
 * The `bst_dispose` function frees a given BST.
 *
 * @param node: the root of the BST
 * 
 * The function makes sure that the nodes in the BST are freed.
 */
void bst_dispose(struct bst_node *node)
{
    if (node != 0) {
        bst_dispose(node->left);
        bst_dispose(node->right);
        free(node);
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of BST.
 */
int main()
{
    struct bst_node *tree = bst_create();
    tree = bst_insert(tree, 10);
    tree = bst_insert(tree, 5);
    tree = bst_insert(tree, 15);
    tree = bst_insert(tree, 8);
    tree = bst_insert(tree, 12);

    bool found8 = bst_search(tree, 8);
    bool found20 = bst_search(tree, 20);

    bst_traverse(tree);

    bst_dispose(tree);
    return 0;
}
