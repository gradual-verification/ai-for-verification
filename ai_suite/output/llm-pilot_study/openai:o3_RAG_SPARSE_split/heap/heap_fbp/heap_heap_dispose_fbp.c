#include "stdlib.h"
#include "limits.h"

struct heap_node {
    int value;
    struct heap_node *left;
    struct heap_node *right;
};

/*@
predicate heap(struct heap_node *node, int min_val) =
    node == 0 ?
        min_val == INT_MAX
    :
        malloc_block_heap_node(node) &*&
        node->value |-> ?v &*&
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        heap(left, ?left_min) &*&
        heap(right, ?right_min) &*&
        v <= left_min &*& v <= right_min &*&
        min_val == v;
@*/

/*@
  The function recursively disposes a binary heap.
  It consumes the `heap` predicate and frees every
  dynamically-allocated node that is part of the heap.
@*/
void heap_dispose(struct heap_node *node)
    //@ requires heap(node, _);
    //@ ensures true;
{
    if (node == 0) {
        /* When `node` is null the predicate contains no
           heap memory – we simply open it and return. */
        //@ open heap(node, _);
    } else {
        /* Open the predicate so we can access the fields. */
        //@ open heap(node, _);

        /* Recursively dispose the left and right sub-heaps. */
        heap_dispose(node->left);
        heap_dispose(node->right);

        /* After the recursive calls we still own:
             - malloc_block_heap_node(node)
             - node->value |-> _
             - node->left  |-> _
             - node->right |-> _
           These chunks are exactly what `free` needs
           (VeriFast’s auto‐conversion turns them into the
           generic `chars_` representation), so the call verifies. */
        free(node);
    }
}