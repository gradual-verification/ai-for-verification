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
        struct bst_node *left = node->left;
        struct bst_node *right = node->right;
        bst_traverse(left);
        bst_traverse(right);
        //@ close bst(node, min, max);
    }
}