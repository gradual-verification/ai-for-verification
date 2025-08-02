#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@
// Define a predicate for a binary search tree
// A BST has the property that all values in the left subtree are less than the node's value
// and all values in the right subtree are greater than the node's value
predicate bst(struct bst_node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->value |-> ?value &*&
        malloc_block_bst_node(node) &*&
        bst(left, ?leftValues) &*&
        bst(right, ?rightValues) &*&
        values == append(leftValues, cons(value, rightValues)) &*&
        forall(leftValues, (lt)(value)) == true &*&
        forall(rightValues, (gt)(value)) == true;

// Helper fixpoints for BST property
fixpoint bool lt(int x, int y) { return y < x; }
fixpoint bool gt(int x, int y) { return y > x; }
@*/

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
//@ requires bst(node, ?values);
//@ ensures bst(node, values);
{
    if (node == 0) {
        //@ // Empty tree case - nothing to do
    } else {
        //@ open bst(node, values);
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
        //@ close bst(node, values);
    }
}