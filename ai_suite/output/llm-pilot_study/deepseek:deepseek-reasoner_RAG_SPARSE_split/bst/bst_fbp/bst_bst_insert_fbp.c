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

struct bst_node *bst_insert(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max) &*& min < value &*& value < max;
    //@ ensures bst(result, min, max);
{
    if (node == 0) {
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        //@ close bst(0, min, value);
        //@ close bst(0, value, max);
        //@ close bst(new_node, min, max);
        return new_node;
    } else {
        //@ open bst(node, min, max);
        if (value < node->value) {
            struct bst_node *left = bst_insert(node->left, value);
            //@ assert bst(left, min, node->value);
            node->left = left;
        } else if (value > node->value) {
            struct bst_node *right = bst_insert(node->right, value);
            //@ assert bst(right, node->value, max);
            node->right = right;
        } else {
            // Value already exists, no change needed
        }
        //@ close bst(node, min, max);
        return node;
    }
}