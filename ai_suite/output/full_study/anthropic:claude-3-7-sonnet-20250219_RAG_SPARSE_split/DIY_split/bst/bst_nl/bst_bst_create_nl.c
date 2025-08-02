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
predicate bst(struct bst_node *node; list<int> values) =
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

// Helper fixpoints for BST property verification
fixpoint bool lt(int x, int y) { return x < y; }
fixpoint bool gt(int x, int y) { return x > y; }
@*/

/***
 * Description:
 * The `bst_create` function creates an empty BST.
 *
 *
 * The function makes sure that the new node is the root of a BST. 
 */
struct bst_node *bst_create()
    //@ requires true;
    //@ ensures bst(result, nil);
{
    return 0;
    //@ close bst(0, nil);
}