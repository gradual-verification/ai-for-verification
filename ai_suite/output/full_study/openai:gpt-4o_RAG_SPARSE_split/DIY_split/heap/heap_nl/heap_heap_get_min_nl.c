#include "stdlib.h"
#include "limits.h"

/***
 * Description:
 * The `heap_node` is a node of a simple min-heap, where its value <= the min-value of left and right sub-heap.
 * The heap doesn't need to be balanced.
 */
struct heap_node {
    int value;
    struct heap_node *left;
    struct heap_node *right;
};

/*@
predicate heap(struct heap_node *h, int minValue) =
    h == 0 ?
        minValue == INT_MAX
    :
        h->value |-> ?v &*& h->left |-> ?l &*& h->right |-> ?r &*&
        malloc_block_heap_node(h) &*&
        heap(l, ?minLeft) &*& heap(r, ?minRight) &*&
        v <= minLeft &*& v <= minRight &*&
        minValue == v;
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `heap_get_min` function gets the minimum value of a given heap.
 *
 * @param h: the given node of a heap that is not null
 *
 * It makes sure that the heap property is unchanged and the return value is the minimum value of the heap. 
 */
int heap_get_min(struct heap_node *h)
    //@ requires heap(h, ?minValue);
    //@ ensures heap(h, minValue) &*& result == minValue;
{
    //@ open heap(h, minValue);
    int val = h->value;
    //@ close heap(h, minValue);
    return val;
}