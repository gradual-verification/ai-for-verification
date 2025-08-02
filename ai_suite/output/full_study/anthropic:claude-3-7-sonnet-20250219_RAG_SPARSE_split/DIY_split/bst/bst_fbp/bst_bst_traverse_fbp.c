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
        // Base case: empty tree
        // Nothing to do here
    } else {
        // Open the bst predicate to access the node's fields
        //@ open bst(node, min, max);
        
        int val = node->value;
        
        // Recursively traverse the left subtree
        bst_traverse(node->left);
        
        // Recursively traverse the right subtree
        bst_traverse(node->right);
        
        // Close the bst predicate to restore the invariant
        //@ close bst(node, min, max);
    }
}