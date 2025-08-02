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
    node == 0 ? true :
    node->left |-> ?left &*& node->right |-> ?right &*& node->value |-> _ &*&
    malloc_block_bst_node(node) &*&
    bst(left) &*& bst(right);
@*/

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
    //@ requires bst(node);
    //@ ensures true;
{
    if (node != 0) {
        //@ open bst(node);
        bst_dispose(node->left);
        bst_dispose(node->right);
        free(node);
    }
}