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
        node->value |-> ?v &*& min < v &*& v < max &*&
        node->left |-> ?left &*& node->right |-> ?right &*&
        bst(left, min, v) &*& bst(right, v, max);
@*/

// TODO: make this function pass the verification
bool bst_search(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max) &*& result == (exists<int>(?v; v == value && bst(node, min, max) && bst_contains(node, value)));
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

fixpoint bool bst_contains(struct bst_node *node, int value) {
    switch (node) {
        case 0: return false;
        case struct bst_node(left, right, v):
            return v == value || (value < v ? bst_contains(left, value) : bst_contains(right, value));
    }
}

lemma void bst_contains_preserved(struct bst_node *node, int min, int max, int value)
    requires bst(node, min, max);
    ensures bst(node, min, max) &*& bst_contains(node, value) == (exists<int>(?v; v == value && bst(node, min, max) && bst_contains(node, value)));
{
    open bst(node, min, max);
    if (node != 0) {
        bst_contains_preserved(node->left, min, node->value, value);
        bst_contains_preserved(node->right, node->value, max, value);
    }
    close bst(node, min, max);
}

@*/