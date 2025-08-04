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
// A predicate to represent a min-heap.
// It captures the pointer `h`, the list of all values `vs` in the heap, and the minimum value `min_val`.
predicate heap(struct heap_node *h, list<int> vs, int min_val) =
    h == 0 ?
        // An empty heap has no values, and its minimum is the maximum integer value.
        vs == nil &*& min_val == INT_MAX
    :
        // A non-empty heap has a root node.
        h->value |-> ?v &*&
        h->left |-> ?l &*&
        h->right |-> ?r &*&
        malloc_block_heap_node(h) &*&
        // Recursively describe the left and right sub-heaps.
        heap(l, ?lvs, ?l_min) &*&
        heap(r, ?rvs, ?r_min) &*&
        // The list of values is the root's value plus the values from sub-heaps.
        vs == cons(v, append(lvs, rvs)) &*&
        // The min-heap property: root's value is less than or equal to children's minimums.
        v <= l_min &*& v <= r_min &*&
        // The minimum value of this heap is the root's value.
        min_val == v;
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
    //@ requires heap(h, ?vs, ?min_val) &*& h != 0;
    //@ ensures heap(h, vs, min_val) &*& result == min_val;
{
    //@ open heap(h, vs, min_val);
    int val = h->value;
    //@ close heap(h, vs, min_val);
    return val;
}