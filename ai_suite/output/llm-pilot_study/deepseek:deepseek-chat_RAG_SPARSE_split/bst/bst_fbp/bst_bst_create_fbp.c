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

struct bst_node *bst_create()
    //@ requires true;
    //@ ensures bst(result, INT_MIN, INT_MAX);
{
    //@ close bst(0, INT_MIN, INT_MAX);
    return 0;
}

// Additional BST operations would go here with their specifications

/*@
lemma void bst_merge(struct bst_node *node)
    requires bst(node, ?min, ?max) &*& min <= max;
    ensures bst(node, min, max);
{
    open bst(node, min, max);
    if (node != 0) {
        bst_merge(node->left);
        bst_merge(node->right);
    }
    close bst(node, min, max);
}
@*/