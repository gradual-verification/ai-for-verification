#include "stdlib.h"
#include "stdbool.h"

struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@ 
predicate bst(struct bst_node *node, int min, int max) =
    node == 0 ?
        true
    :
        malloc_block_bst_node(node) &*&
        node->value |-> ?v &*& min < v &*& v < max &*&
        node->left |-> ?left &*& node->right |-> ?right &*&
        bst(left, min, v) &*& bst(right, v, max);
@*/

bool bst_search(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max) &*& result == (t_contains(bst_to_tree(node), value);
{
    if (node == 0) {
        return false;
    }
    else if (node->value == value) {
        return true;
    }
    else if (value < node->value) {
        //@ open bst(node, min, max);
        bool result = bst_search(node->left, value);
        //@ close bst(node, min, max);
        return result;
    }
    else {
        //@ open bst(node, min, max);
        bool result = bst_search(node->right, value);
        //@ close bst(node, min, max);
        return result;
    }
}

/*@
// Helper functions for specification
inductive tree = empty | node(int, tree, tree);

fixpoint bool t_contains(tree t, int value) {
    switch (t) {
        case empty: return false;
        case node(v, l, r): 
            return v == value || 
                   (value < v ? t_contains(l, value) : t_contains(r, value));
    }
}

fixpoint tree bst_to_tree(struct bst_node *node) {
    return node == 0 ? empty : 
           node(node->value, bst_to_tree(node->left), bst_to_tree(node->right));
}

lemma void bst_to_tree_contains(struct bst_node *node, int value)
    requires bst(node, ?min, ?max);
    ensures bst(node, min, max) &*& 
            t_contains(bst_to_tree(node), value) == 
            (node != 0 && (node->value == value || 
                          (value < node->value ? t_contains(bst_to_tree(node->left), value) :
                                               t_contains(bst_to_tree(node->right), value)));
{
    if (node == 0) {
    } else {
        open bst(node, min, max);
        bst_to_tree_contains(node->left, value);
        bst_to_tree_contains(node->right, value);
        close bst(node, min, max);
    }
}
@*/