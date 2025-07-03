#include "stdlib.h"
#include "stdbool.h"

/* ---------- Data structure ---------- */
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/* ---------- Predicate ---------- */
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

/* ---------- Function to verify ---------- */
// TODO: make this function pass the verification
struct bst_node *bst_create()
    //@ requires true;
    //@ ensures bst(result, INT_MIN, INT_MAX);
{
    /* 
       Creating the empty tree: the predicate bst holds for a null
       pointer without requiring any heap chunks.  We therefore just
       close the predicate for 0 and return.
    */
    //@ close bst(0, INT_MIN, INT_MAX);
    return 0;
}