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

// -------------- Verified code --------------

/* 
 * Disposes a binary search tree.
 */
void bst_dispose(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures true;
{
    if (node == 0) {
        /*  When node is null, the bst predicate is just `true`.
            We open it to match the requires/ensures balance. */
        //@ open bst(node, min, max);
    } else {
        /* Open the predicate to gain access to the fields and the
           malloc‐block permission that free() needs. */
        //@ open bst(node, min, max);

        /* Save the child pointers before the recursive calls, because
           after opening the predicate we own them. */
        struct bst_node *l = node->left;
        struct bst_node *r = node->right;

        /* Recursively dispose the sub-trees. The contracts of the
           recursive calls follow from the opened predicate. */
        bst_dispose(l);
        bst_dispose(r);

        /* All permissions required by `free` are now in scope:
           `malloc_block_bst_node(node)`, the value field and the two
           pointer fields have full ownership, so the call verifies. */
        free(node);
    }
}