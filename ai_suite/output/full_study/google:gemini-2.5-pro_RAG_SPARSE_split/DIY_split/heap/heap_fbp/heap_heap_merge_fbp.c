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
        //@ open heap(h1, min1);
        //@ open heap(h2, min2);
        return h2;
    } else if (h1 == 0) {
        //@ open heap(h1, min1);
        return h2;
    } else if (h2 == 0) {
        //@ open heap(h2, min2);
        return h1;
    }

    //@ open heap(h1, min1);
    //@ assert h1->value |-> ?v1 &*& h1->left |-> ?l1 &*& h1->right |-> ?r1 &*& heap(l1, ?lm1) &*& heap(r1, ?rm1) &*& v1 <= lm1 &*& v1 <= rm1 &*& min1 == v1;
    //@ open heap(h2, min2);
    //@ assert h2->value |-> ?v2 &*& h2->left |-> ?l2 &*& h2->right |-> ?r2 &*& heap(l2, ?lm2) &*& heap(r2, ?rm2) &*& v2 <= lm2 &*& v2 <= rm2 &*& min2 == v2;

    struct heap_node *smaller;
    int smaller_val;

    if (h1->value <= h2->value) {
        smaller = h1;
        smaller_val = h1->value;

        //@ close heap(h2, min2);
        struct heap_node *merged_right = heap_merge(r1, h2);
        //@ assert heap(merged_right, ?merged_min) &*& merged_min == (rm1 < min2 ? rm1 : min2);
        smaller->right = merged_right;
        
        //@ close heap(smaller, v1);
    } else {
        smaller = h2;
        smaller_val = h2->value;

        //@ close heap(h1, min1);
        struct heap_node *merged_right = heap_merge(h1, r2);
        //@ assert heap(merged_right, ?merged_min) &*& merged_min == (min1 < rm2 ? min1 : rm2);
        smaller->right = merged_right;
        
        //@ close heap(smaller, v2);
    }

    return smaller;
}