#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@
predicate bst(struct bst_node *node) =
    node == 0 ?
        true
    :
        bst(node->left) &*& bst(node->right);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `bst_create` function creates an empty BST.
 *
 * The function makes sure that the new node is the root of a BST. 
 */
struct bst_node *bst_create()
    //@ requires true;
    //@ ensures bst(result);
{
    //@ close bst(0);
    return 0;
}