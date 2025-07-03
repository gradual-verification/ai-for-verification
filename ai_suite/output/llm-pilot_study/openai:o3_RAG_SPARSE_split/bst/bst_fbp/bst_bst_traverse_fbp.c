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

// Verified inorder traversal of the BST
void bst_traverse(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures  bst(node,  min,  max);
{
    if (node == 0) {
        /* empty tree – nothing to do */
    } else {
        //@ open bst(node, min, max);
        struct bst_node *left  = node->left;
        struct bst_node *right = node->right;
        int val = node->value;     /* just read – not modified */

        bst_traverse(left);
        bst_traverse(right);

        //@ close bst(node, min, max);
    }
}