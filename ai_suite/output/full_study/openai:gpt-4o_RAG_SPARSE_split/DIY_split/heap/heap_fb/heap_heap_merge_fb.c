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
        //@ close heap(0, INT_MAX);
        return h2;
    } else if (h1 == 0) {
        //@ close heap(h2, min2);
        return h2;
    } else if (h2 == 0) {
        //@ close heap(h1, min1);
        return h1;
    }

    struct heap_node *smaller;
    int smaller_val;

    if (h1->value <= h2->value) {
        smaller = h1;
        smaller_val = h1->value;
        //@ open heap(h1, min1);
        //@ open heap(h2, min2);
        struct heap_node *merged_right = heap_merge(h1->right, h2);
        //@ open heap(merged_right, ?merged_min);
        smaller->right = merged_right;
        //@ close heap(smaller, smaller_val);
    } else {
        smaller = h2;
        smaller_val = h2->value;
        //@ open heap(h1, min1);
        //@ open heap(h2, min2);
        struct heap_node *merged_right = heap_merge(h1, h2->right);
        //@ open heap(merged_right, ?merged_min);
        smaller->right = merged_right;
        //@ close heap(smaller, smaller_val);
    }

    return smaller;
}