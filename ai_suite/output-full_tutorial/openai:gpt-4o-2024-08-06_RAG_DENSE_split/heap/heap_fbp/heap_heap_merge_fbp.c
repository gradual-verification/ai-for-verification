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

// TODO: make this function pass the verification
struct heap_node *heap_merge(struct heap_node *h1, struct heap_node *h2)
    //@ requires heap(h1, ?min1) &*& heap(h2, ?min2);
    //@ ensures heap(result, ?new_min) &*& new_min == (min1 < min2 ? min1 : min2);
{
    if (h1 == 0 && h2 == 0) {
        return h2;
    } else if (h1 == 0) {
        return h2;
    } else if (h2 == 0) {
        return h1;
    }

    struct heap_node *smaller;
    int smaller_val;

    if (h1->value <= h2->value) {
        smaller = h1;
        smaller_val = h1->value;

        struct heap_node *merged_right = heap_merge(h1->right, h2);
        //@ open heap(h1->right, _);
        //@ open heap(h2, _);
        //@ close heap(merged_right, _);
        smaller->right = merged_right;
    } else {
        smaller = h2;
        smaller_val = h2->value;

        struct heap_node *merged_right = heap_merge(h1, h2->right);
        //@ open heap(h1, _);
        //@ open heap(h2->right, _);
        //@ close heap(merged_right, _);
        smaller->right = merged_right;
    }

    //@ open heap(smaller->left, _);
    //@ open heap(smaller->right, _);
    //@ close heap(smaller, smaller_val);
    return smaller;
}