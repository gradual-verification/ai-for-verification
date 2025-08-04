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
    //@ open heap(h1, min1);
    //@ open heap(h2, min2);
    if (h1 == 0 && h2 == 0) {
        //@ close heap(h2, min2);
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

        //@ int v1 = h1->value;
        //@ struct heap_node *left1 = h1->left;
        //@ struct heap_node *right1 = h1->right;
        //@ int v2 = h2->value;

        //@ close heap(h2, v2);
        struct heap_node *merged_right = heap_merge(right1, h2);
        //@ open heap(merged_right, ?new_min_r);
        // We need to prove v1 <= new_min_r.
        // From postcondition: new_min_r == (right_min1 < v2 ? right_min1 : v2).
        // We know v1 <= right_min1 (from heap(h1, v1)).
        // We know v1 <= v2 (from the if condition).
        // Therefore, v1 <= min(right_min1, v2), so v1 <= new_min_r.
        smaller->right = merged_right;
        //@ close heap(smaller, v1);
    } else {
        smaller = h2;
        smaller_val = h2->value;

        //@ int v1 = h1->value;
        //@ int v2 = h2->value;
        //@ struct heap_node *left2 = h2->left;
        //@ struct heap_node *right2 = h2->right;

        //@ close heap(h1, v1);
        struct heap_node *merged_right = heap_merge(h1, right2);
        //@ open heap(merged_right, ?new_min_r);
        // We need to prove v2 <= new_min_r.
        // From postcondition: new_min_r == (v1 < right_min2 ? v1 : right_min2).
        // We know v2 < v1 (from the if condition).
        // We know v2 <= right_min2 (from heap(h2, v2)).
        // Therefore, v2 <= min(v1, right_min2), so v2 <= new_min_r.
        smaller->right = merged_right;
        //@ close heap(smaller, v2);
    }

    return smaller;
}