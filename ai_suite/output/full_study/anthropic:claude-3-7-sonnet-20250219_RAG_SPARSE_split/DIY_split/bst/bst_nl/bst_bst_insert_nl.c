#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@
// Predicate to represent a valid BST with values in a specific range
predicate bst_node(struct bst_node *node, int min, int max) =
    node == 0 ?
        true
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->value |-> ?value &*&
        malloc_block_bst_node(node) &*&
        min < value &*& value < max &*&
        bst_node(left, min, value) &*&
        bst_node(right, value, max);
@*/

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
//@ requires bst_node(node, ?min, ?max) &*& min < value &*& value < max;
//@ ensures bst_node(result, min, max);
{
    if (node == 0) {
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        //@ close bst_node(0, min, value);
        //@ close bst_node(0, value, max);
        //@ close bst_node(new_node, min, max);
        return new_node;
    } else {
        //@ open bst_node(node, min, max);
        if (value < node->value) {
            node->left = bst_insert(node->left, value);
            //@ close bst_node(node, min, max);
        } else if (value > node->value) {
            node->right = bst_insert(node->right, value);
            //@ close bst_node(node, min, max);
        } else {   
            //@ close bst_node(node, min, max);
        }

        return node;
    }
}