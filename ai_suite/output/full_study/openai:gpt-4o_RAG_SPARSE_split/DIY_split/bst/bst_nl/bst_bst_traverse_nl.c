#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@
predicate bst(struct bst_node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->left |-> ?left &*& node->right |-> ?right &*& node->value |-> ?value &*&
        malloc_block_bst_node(node) &*&
        bst(left, ?leftValues) &*& bst(right, ?rightValues) &*&
        forall(leftValues, (lt)(value)) == true &*&
        forall(rightValues, (gt)(value)) == true &*&
        values == append(leftValues, cons(value, rightValues));

fixpoint bool lt(int a, int b) { return a < b; }
fixpoint bool gt(int a, int b) { return a > b; }
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
        //@ close bst(0, nil);
    } else {
        //@ open bst(node, values);
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
        //@ close bst(node, values);
    }
}