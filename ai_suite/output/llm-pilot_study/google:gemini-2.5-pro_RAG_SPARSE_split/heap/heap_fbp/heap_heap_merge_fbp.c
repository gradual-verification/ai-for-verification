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
    //@ assert h1->value |-> ?v1 &*& h1->left |-> ?left1 &*& h1->right |-> ?right1;
    //@ assert heap(left1, ?left_min1) &*& heap(right1, ?right_min1);
    //@ assert v1 <= left_min1 &*& v1 <= right_min1 &*& min1 == v1;
    
    //@ open heap(h2, min2);
    //@ assert h2->value |-> ?v2 &*& h2->left |-> ?left2 &*& h2->right |-> ?right2;
    //@ assert heap(left2, ?left_min2) &*& heap(right2, ?right_min2);
    //@ assert v2 <= left_min2 &*& v2 <= right_min2 &*& min2 == v2;

    struct heap_node *smaller;
    int smaller_val;

    if (h1->value <= h2->value) {
        smaller = h1;
        smaller_val = h1->value;

        //@ close heap(h2, v2);
        struct heap_node *merged_right = heap_merge(h1->right, h2);
        //@ assert heap(merged_right, ?merged_min) &*& merged_min == (right_min1 < v2 ? right_min1 : v2);
        smaller->right = merged_right;
        
        //@ assert v1 <= right_min1;
        //@ assert v1 <= v2;
        //@ assert v1 <= merged_min;
        
        //@ close heap(smaller, v1);
    } else {
        smaller = h2;
        smaller_val = h2->value;

        //@ close heap(h1, v1);
        struct heap_node *merged_right = heap_merge(h1, h2->right);
        //@ assert heap(merged_right, ?merged_min) &*& merged_min == (v1 < right_min2 ? v1 : right_min2);
        smaller->right = merged_right;

        //@ assert v2 <= right_min2;
        //@ assert v2 < v1;
        //@ assert v2 <= merged_min;
        
        //@ close heap(smaller, v2);
    }

    return smaller;
}