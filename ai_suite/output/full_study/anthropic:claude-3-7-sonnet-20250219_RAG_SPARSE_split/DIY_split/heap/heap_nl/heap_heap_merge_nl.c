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
// Define a predicate for a heap structure
predicate heap(struct heap_node *h; int min_value) =
    h == 0 ?
        min_value == INT_MAX
    :
        h->value |-> ?v &*& h->left |-> ?l &*& h->right |-> ?r &*& 
        malloc_block_heap_node(h) &*&
        heap(l, ?lmin) &*& heap(r, ?rmin) &*&
        v <= lmin &*& v <= rmin &*&
        min_value == v;
@*/

/***
 * Description:
 * The `heap_merge` function merges the two heaps into one heap.
 *
 * @param h1, h2: the given nodes of two heaps
 *
 * The function makes sure that the new heap has its value as the minimum value of two original heaps.
 */
struct heap_node *heap_merge(struct heap_node *h1, struct heap_node *h2)
//@ requires heap(h1, ?min1) &*& heap(h2, ?min2);
//@ ensures heap(result, ?min_result) &*& min_result == (min1 <= min2 ? min1 : min2);
{
    if (h1 == 0 && h2 == 0) {
        //@ close heap(h2, INT_MAX);
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
        //@ assert heap(merged_right, ?merged_min);
        //@ assert h1->left |-> ?l;
        //@ assert heap(l, ?lmin);
        
        smaller->right = merged_right;
        
        //@ assert smaller_val <= lmin;
        //@ assert smaller_val <= merged_min;
        //@ close heap(smaller, smaller_val);
    } else {
        smaller = h2;
        smaller_val = h2->value;

        struct heap_node *merged_right = heap_merge(h1, h2->right);
        //@ assert heap(merged_right, ?merged_min);
        //@ assert h2->left |-> ?l;
        //@ assert heap(l, ?lmin);
        
        smaller->right = merged_right;
        
        //@ assert smaller_val <= lmin;
        //@ assert smaller_val <= merged_min;
        //@ close heap(smaller, smaller_val);
    }

    return smaller;
}