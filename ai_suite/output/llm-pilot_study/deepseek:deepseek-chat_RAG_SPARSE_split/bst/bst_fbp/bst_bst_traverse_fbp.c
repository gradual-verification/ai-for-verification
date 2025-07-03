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

void bst_traverse(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max);
{
    if (node == 0) {
        //@ open bst(node, min, max);
        //@ close bst(node, min, max);
    } else {
        //@ open bst(node, min, max);
        int val = node->value;
        bst_traverse(node->left);
        //@ assert bst(node->left, min, val);
        bst_traverse(node->right);
        //@ assert bst(node->right, val, max);
        //@ close bst(node, min, max);
    }
}