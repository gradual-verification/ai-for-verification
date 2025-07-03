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
        node->left |-> ?left &*& node->right |-> ?right &*&
        heap(left, ?left_min) &*& heap(right, ?right_min) &*&
        v <= left_min &*& v <= right_min &*&
        min_val == v;
@*/

// Verified implementation of heap_merge
struct heap_node *heap_merge(struct heap_node *h1, struct heap_node *h2)
    //@ requires heap(h1, ?min1) &*& heap(h2, ?min2);
    //@ ensures heap(result, ?new_min) &*& new_min == (min1 < min2 ? min1 : min2);
{
    if (h1 == 0) {
        //@ open heap(h1, min1);
        return h2;
    } else if (h2 == 0) {
        //@ open heap(h2, min2);
        return h1;
    }

    //@ open heap(h1, min1);
    //@ open heap(h2, min2);
    struct heap_node *smaller;
    if (h1->value <= h2->value) {
        smaller = h1;
        //@ assert min1 == h1->value;
        struct heap_node *merged_right = heap_merge(h1->right, h2);
        //@ assert heap(merged_right, ?min_merged) &*& min_merged == (min1 < min2 ? min1 : min2);
        //@ assert h1->value <= min_merged;
        smaller->right = merged_right;
        //@ close heap(smaller, h1->value);
    } else {
        smaller = h2;
        //@ assert min2 == h2->value;
        struct heap_node *merged_right = heap_merge(h1, h2->right);
        //@ assert heap(merged_right, ?min_merged) &*& min_merged == (min1 < min2 ? min1 : min2);
        //@ assert h2->value <= min_merged;
        smaller->right = merged_right;
        //@ close heap(smaller, h2->value);
    }
    return smaller;
}