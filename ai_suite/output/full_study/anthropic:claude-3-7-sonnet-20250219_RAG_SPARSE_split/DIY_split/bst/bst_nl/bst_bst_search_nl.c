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
        // BST property: all values in left subtree are less than node's value
        (forall(leftValues, (lt)(value))) &*&
        // BST property: all values in right subtree are greater than node's value
        (forall(rightValues, (gt)(value)));

// Helper fixpoints for BST property
fixpoint bool lt(int x, int y) { return y < x; }
fixpoint bool gt(int x, int y) { return y > x; }

// Predicate to check if a value is in a list
fixpoint bool mem(int x, list<int> xs) {
    switch(xs) {
        case nil: return false;
        case cons(h, t): return h == x || mem(x, t);
    }
}

// Lemma to prove that if a value is in a BST, the search will find it
lemma void bst_search_mem(struct bst_node *node, int value, list<int> values)
    requires bst(node, values) &*& mem(value, values) == true;
    ensures bst(node, values) &*& bst_search(node, value) == true;
{
    if (node == 0) {
        open bst(node, values);
        assert values == nil;
        assert mem(value, nil) == false;
        assert false;
    } else {
        open bst(node, values);
        if (node->value == value) {
            close bst(node, values);
        } else if (value < node->value) {
            // Value must be in left subtree
            assert mem(value, append(leftValues, cons(node->value, rightValues))) == true;
            assert mem(value, leftValues) == true;
            bst_search_mem(left, value, leftValues);
            close bst(node, values);
        } else {
            // Value must be in right subtree
            assert mem(value, append(leftValues, cons(node->value, rightValues))) == true;
            assert mem(value, rightValues) == true;
            bst_search_mem(right, value, rightValues);
            close bst(node, values);
        }
    }
}

// Lemma to prove that if a value is not in a BST, the search will not find it
lemma void bst_search_not_mem(struct bst_node *node, int value, list<int> values)
    requires bst(node, values) &*& mem(value, values) == false;
    ensures bst(node, values) &*& bst_search(node, value) == false;
{
    if (node == 0) {
        open bst(node, values);
        close bst(node, values);
    } else {
        open bst(node, values);
        if (node->value == value) {
            assert mem(value, values) == true;
            assert false;
        } else if (value < node->value) {
            // Value must not be in left subtree
            assert mem(value, leftValues) == false;
            bst_search_not_mem(left, value, leftValues);
            close bst(node, values);
        } else {
            // Value must not be in right subtree
            assert mem(value, rightValues) == false;
            bst_search_not_mem(right, value, rightValues);
            close bst(node, values);
        }
    }
}
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
bool bst_search(struct bst_node *node, int value)
    //@ requires bst(node, ?values);
    //@ ensures bst(node, values) &*& result == mem(value, values);
{
    if (node == 0) {
        //@ open bst(node, values);
        //@ close bst(node, values);
        return false;
    }
    else if (node->value == value) {
        //@ open bst(node, values);
        //@ close bst(node, values);
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