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
// Define a predicate for a heap node
predicate heap(struct heap_node *h; int min_value) =
    h == 0 ?
        min_value == INT_MAX
    :
        h->value |-> ?value &*&
        h->left |-> ?left &*&
        h->right |-> ?right &*&
        malloc_block_heap_node(h) &*&
        heap(left, ?left_min) &*&
        heap(right, ?right_min) &*&
        value <= left_min &*&
        value <= right_min &*&
        min_value == value;
@*/

/***
 * Description:
 * The `heap_get_min` function gets the minimum value of a given heap.
 *
 * @param h1, h2: the given node of a heap that is not null
 *
 * It makes sure that the heap property is unchanged and the return value is the minimum value of the heap. 
 */
int heap_get_min(struct heap_node *h)
//@ requires heap(h, ?min_value) &*& h != 0;
//@ ensures heap(h, min_value) &*& result == min_value;
{
    //@ open heap(h, min_value);
    int val = h->value;
    //@ close heap(h, min_value);
    return val;
}