#include "stdlib.h"
#include "stdbool.h"

/*@
// An abstract representation of a binary search tree.
inductive bst =
    | empty
    | node(int value, bst left, bst right);

// Returns the minimum value in a non-empty BST.
// It is the caller's responsibility to ensure the bst is not empty.
fixpoint int bst_min(bst b) {
    switch (b) {
        case empty: return 0; // Should not be reached for valid BSTs.
        case node(v, l, r): return l == empty ? v : bst_min(l);
    }
}

// Returns the maximum value in a non-empty BST.
// It is the caller's responsibility to ensure the bst is not empty.
fixpoint int bst_max(bst b) {
    switch (b) {
        case empty: return 0; // Should not be reached for valid BSTs.
        case node(v, l, r): return r == empty ? v : bst_max(r);
    }
}

// Checks if a bst satisfies the binary search tree property.
// All values in the left subtree must be less than the node's value.
// All values in the right subtree must be greater than the node's value.
// This property implies that all values in the tree are unique.
fixpoint bool is_bst(bst b) {
    switch (b) {
        case empty: return true;
        case node(v, l, r):
            return
                is_bst(l) &*&
                is_bst(r) &*&
                (l == empty ? true : bst_max(l) < v) &*&
                (r == empty ? true : v < bst_min(r));
    }
}

// A predicate that connects the C struct bst_node to the abstract bst model,
// and asserts that the tree satisfies the BST property.
predicate bst_pred(struct bst_node *n; bst b) =
    (n == 0 ?
        b == empty
    :
        n->value |-> ?v &*&
        n->left |-> ?left_ptr &*&
        n->right |-> ?right_ptr &*&
        malloc_block_bst_node(n) &*&
        bst_pred(left_ptr, ?left_bst) &*&
        bst_pred(right_ptr, ?right_bst) &*&
        b == node(v, left_bst, right_bst)
    ) &*& is_bst(b) == true;

@*/

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
    //@ requires true;
    //@ ensures bst_pred(result, empty);
{
    //@ close bst_pred(0, empty);
    return 0;
}