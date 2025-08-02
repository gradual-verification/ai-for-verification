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
 * The `bst_insert` function inserts a value into the BST.
 *
 * @param node: the root of the BST
 * @param value: the value to be inserted
 * 
 * The function requires that the value is within the range of possible MAX and MIN value of BST,
 * and ensures that the returned node is still a root of a BST.
 */
struct bst_node *bst_insert(struct bst_node *node, int value)
    //@ requires bst(node, ?values) &*& forall(values, (neq)(value)) == true;
    //@ ensures bst(result, append(values, cons(value, nil)));
{
    if (node == 0) {
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        //@ close bst(new_node, cons(value, nil));
        return new_node;
    } else {
        //@ open bst(node, values);
        if (value < node->value) {
            node->left = bst_insert(node->left, value);
        } else if (value > node->value) {
            node->right = bst_insert(node->right, value);
        } else {
            // Value already exists, do nothing
        }
        //@ close bst(node, append(values, cons(value, nil)));
        return node;
    }
}