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

/*  
   Verified (read-only) binary-search-tree lookup.
   The tree is not modified, therefore we must return the original
   bst predicate to the caller. All that is required is to open the
   predicate when the node is known to be non-null, and to close it
   again before every return.
*/
// TODO: make this function pass the verification
bool bst_search(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max);
    //@ ensures  bst(node,  min,  max);
{
    /*  Empty subtree: nothing found, predicate untouched. */
    if (node == 0) {
        return false;
    } 
    /*  Non-empty subtree: open the predicate once and keep the
        chunks on the heap while searching recursively.            */
    else
    {
        //@ open bst(node, min, max);
        int v                     = node->value;
        struct bst_node *leftSub  = node->left;
        struct bst_node *rightSub = node->right;

        bool result;
        if (v == value) {
            result = true;
        } 
        else if (value < v) {
            /*  Pass the ownership of the left-subtree chunk to the
                recursive call; it is returned unchanged by the
                post-condition of bst_search.                       */
            result = bst_search(leftSub, value);
        } 
        else {
            result = bst_search(rightSub, value);
        }

        /*  Re-assemble the predicate for this node and return. */
        //@ close bst(node, min, max);
        return result;
    }
}