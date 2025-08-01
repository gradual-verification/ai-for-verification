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

// TODO: make this function pass the verification
/***
 * Description:
 * The `heap_get_min` function gets the minimum value of a given heap.
 *
 * @param h1, h2: the given node of a heap that is not null
 *
 * It makes sure that the heap property is unchanged and the return value is the minimum value of the heap. 
 */
int heap_get_min(struct heap_node *h)
{
    int val = h->value;
    return val;
}
