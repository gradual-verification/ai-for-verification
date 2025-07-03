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
        //@ open bst(node, min, max);
        bst_dispose(node->left);
        bst_dispose(node->right);
        //@ open malloc_block_bst_node(node);
        free(node);
    }
}