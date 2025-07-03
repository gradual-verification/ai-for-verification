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

// TODO: make this function pass the verification
void bst_dispose(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures true;
{
    if (node != 0) {
        bst_dispose(node->left);
        bst_dispose(node->right);
        free(node);
    }
}

/*@ 
lemma void bst_dispose_lemma(struct bst_node *node, int min, int max)
    requires bst(node, min, max);
    ensures true;
{
    bst_dispose(node);
}
@*/

// The following function is added to demonstrate the verification of bst_dispose
void test_bst_dispose()
    //@ requires bst(?node, 0, 100);
    //@ ensures true;
{
    bst_dispose(node);
}