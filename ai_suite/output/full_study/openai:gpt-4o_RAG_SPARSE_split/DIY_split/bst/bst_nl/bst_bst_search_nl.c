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
        node->value |-> ?v &*& node->left |-> ?left &*& node->right |-> ?right &*&
        malloc_block_bst_node(node) &*&
        bst(left, ?leftValues) &*& bst(right, ?rightValues) &*&
        values == append(leftValues, cons(v, rightValues)) &*&
        forall(leftValues, (lt)(v)) == true &*&
        forall(rightValues, (gt)(v)) == true;

fixpoint bool lt(int a, int b) { return a < b; }
fixpoint bool gt(int a, int b) { return a > b; }
@*/

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
/*@
requires bst(node, ?values);
ensures bst(node, values) &*& result == mem(value, values);
@*/
bool bst_search(struct bst_node *node, int value)
{
    if (node == 0) {
        return false;
    }
    else if (node->value == value) {
        return true;
    }
    else if (value < node->value) {
        //@ open bst(node, values);
        bool result = bst_search(node->left, value);
        //@ close bst(node, values);
        return result;
    }
    else {
        //@ open bst(node, values);
        bool result = bst_search(node->right, value);
        //@ close bst(node, values);
        return result;
    }
}