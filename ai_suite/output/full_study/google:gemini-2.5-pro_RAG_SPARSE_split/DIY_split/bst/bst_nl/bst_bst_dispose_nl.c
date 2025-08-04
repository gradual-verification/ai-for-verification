#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@

fixpoint bool forall_lt(list<int> vs, int max) {
    switch(vs) {
        case nil: return true;
        case cons(h, t): return h < max && forall_lt(t, max);
    }
}

fixpoint bool forall_gt(list<int> vs, int min) {
    switch(vs) {
        case nil: return true;
        case cons(h, t): return h > min && forall_gt(t, min);
    }
}

predicate bst(struct bst_node *node; list<int> values) =
    node == 0 ?
        values == nil
    :
        node->left |-> ?l &*&
        node->right |-> ?r &*&
        node->value |-> ?v &*&
        malloc_block_bst_node(node) &*&
        bst(l, ?l_values) &*&
        bst(r, ?r_values) &*&
        forall_lt(l_values, v) == true &*&
        forall_gt(r_values, v) == true &*&
        values == append(l_values, cons(v, r_values));

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
    //@ requires bst(node, ?values);
    //@ ensures emp;
{
    if (node != 0) {
        //@ open bst(node, values);
        bst_dispose(node->left);
        bst_dispose(node->right);
        free(node);
    } else {
        //@ open bst(node, values);
    }
}