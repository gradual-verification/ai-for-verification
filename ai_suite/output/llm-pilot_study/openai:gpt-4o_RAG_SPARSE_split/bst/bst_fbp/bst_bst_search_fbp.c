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
bool bst_search(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max) &*& result == (exists<int>(v) &*& v == value);
{
    if (node == 0) {
        return false;
    }
    else if (node->value == value) {
        return true;
    }
    else if (value < node->value) {
        //@ open bst(node, min, max);
        //@ assert node->left |-> ?left;
        bool result = bst_search(node->left, value);
        //@ close bst(node, min, max);
        return result;
    }
    else {
        //@ open bst(node, min, max);
        //@ assert node->right |-> ?right;
        bool result = bst_search(node->right, value);
        //@ close bst(node, min, max);
        return result;
    }
}