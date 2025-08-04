#include "stdlib.h"
#include "stdbool.h"

/*@
// An abstract representation of a binary search tree's structure and values.
inductive bst = bst_empty | bst_node(bst left, int value, bst right);

// A fixpoint function to check if an abstract bst satisfies the ordering property within given bounds.
// The strict inequalities ensure that all values in the tree are unique.
fixpoint bool is_bst(bst b, int min_val, int max_val) {
    switch (b) {
        case bst_empty:
            return true;
        case bst_node(l, v, r):
            return min_val < v && v < max_val &&
                   is_bst(l, min_val, v) &&
                   is_bst(r, v, max_val);
    }
}

// A fixpoint function that mirrors the search logic on the abstract bst.
fixpoint bool bst_contains(bst b, int val) {
    switch (b) {
        case bst_empty:
            return false;
        case bst_node(l, v, r):
            return v == val || (val < v ? bst_contains(l, val) : bst_contains(r, val));
    }
}

// A predicate that links the C struct bst_node to the abstract bst model.
// It represents ownership of a tree or subtree.
predicate bst_node_inv(struct bst_node *node; bst b) =
    node == 0 ?
        b == bst_empty
    :
        node->left |-> ?l &*&
        node->right |-> ?r &*&
        node->value |-> ?v &*&
        malloc_block_bst_node(node) &*&
        bst_node_inv(l, ?bl) &*&
        bst_node_inv(r, ?br) &*&
        b == bst_node(bl, v, br);

// A lemma to prove that if a tree is a BST within certain bounds, it is also a BST within wider bounds.
lemma void is_bst_weaken(bst b, int min1, int max1, int min2, int max2)
    requires is_bst(b, min1, max1) == true &*& min2 <= min1 &*& max1 <= max2;
    ensures is_bst(b, min2, max2) == true;
{
    switch(b) {
        case bst_empty:
        case bst_node(l, v, r):
            is_bst_weaken(l, min1, v, min2, v);
            is_bst_weaken(r, v, max1, v, max2);
    }
}
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
 * The `bst_search` function searches a value in the given BST.
 *
 * @param node: the root of the BST
 * @param value: the value to be searched
 * 
 * The function makes sure that the BST is still valid after the search operation,
 */
bool bst_search(struct bst_node *node, int value)
    //@ requires bst_node_inv(node, ?b) &*& is_bst(b, INT_MIN, INT_MAX) == true;
    //@ ensures bst_node_inv(node, b) &*& result == bst_contains(b, value);
{
    //@ open bst_node_inv(node, b);
    if (node == 0) {
        //@ close bst_node_inv(node, b);
        return false;
    }
    else {
        if (node->value == value) {
            //@ close bst_node_inv(node, b);
            return true;
        }
        else if (value < node->value) {
            /*@
            switch(b) {
                case bst_empty:
                case bst_node(bl, v, br):
                    is_bst_weaken(bl, INT_MIN, v, INT_MIN, INT_MAX);
            }
            @*/
            bool result = bst_search(node->left, value);
            //@ close bst_node_inv(node, b);
            return result;
        }
        else {
            /*@
            switch(b) {
                case bst_empty:
                case bst_node(bl, v, br):
                    is_bst_weaken(br, v, INT_MAX, INT_MIN, INT_MAX);
            }
            @*/
            bool result = bst_search(node->right, value);
            //@ close bst_node_inv(node, b);
            return result;
        }
    }
}