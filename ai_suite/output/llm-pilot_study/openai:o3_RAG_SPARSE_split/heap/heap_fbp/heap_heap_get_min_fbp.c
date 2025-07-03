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

// Verified: returns the minimal element stored in a non-empty heap
int heap_get_min(struct heap_node *h)
    //@ requires heap(h, ?min_val) &*& h != 0;
    //@ ensures heap(h, min_val) &*& result == min_val;
{
    //@ open heap(h, min_val);                // expose fields of the root node
    int val = h->value;                       // root contains overall minimum
    //@ assert val == min_val;                // establish correspondence
    //@ close heap(h, min_val);               // re-assemble the heap predicate
    return val;
}