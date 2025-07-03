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

struct heap_node *heap_merge(struct heap_node *h1, struct heap_node *h2)
    //@ requires heap(h1, ?min1) &*& heap(h2, ?min2);
    //@ ensures heap(result, ?new_min) &*& new_min == (min1 < min2 ? min1 : min2);
{
    if (h1 == 0 && h2 == 0) {
        //@ close heap(0, INT_MAX);
        return h2;
    } else if (h1 == 0) {
        return h2;
    } else if (h2 == 0) {
        return h1;
    }

    struct heap_node *smaller;
    int smaller_val;

    //@ open heap(h1, min1);
    //@ open heap(h2, min2);
    
    if (h1->value <= h2->value) {
        smaller = h1;
        smaller_val = h1->value;

        struct heap_node *merged_right = heap_merge(h1->right, h2);
        //@ assert heap(merged_right, ?merged_right_min);
        //@ assert merged_right_min == (h1->right == 0 ? (h2 == 0 ? INT_MAX : min2) : (min2 < ?right_min1 ? min2 : right_min1));
        
        smaller->right = merged_right;
        
        //@ assert smaller_val <= ?left_min1;
        //@ assert smaller_val <= merged_right_min;
        //@ close heap(smaller, smaller_val);
    } else {
        smaller = h2;
        smaller_val = h2->value;

        struct heap_node *merged_right = heap_merge(h1, h2->right);
        //@ assert heap(merged_right, ?merged_right_min);
        //@ assert merged_right_min == (h1 == 0 ? (h2->right == 0 ? INT_MAX : ?right_min2) : (min1 < ?right_min2 ? min1 : right_min2));
        
        smaller->right = merged_right;
        
        //@ assert smaller_val <= ?left_min2;
        //@ assert smaller_val <= merged_right_min;
        //@ close heap(smaller, smaller_val);
    }

    return smaller;
}