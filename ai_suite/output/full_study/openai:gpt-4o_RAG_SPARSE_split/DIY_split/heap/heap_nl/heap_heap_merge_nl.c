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
predicate heap(struct heap_node *node, int minValue) =
    node == 0 ?
        minValue == INT_MAX
    :
        node->value |-> ?value &*& node->left |-> ?left &*& node->right |-> ?right &*&
        malloc_block_heap_node(node) &*&
        heap(left, ?leftMin) &*& heap(right, ?rightMin) &*&
        value <= leftMin &*& value <= rightMin &*&
        minValue == value;
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `heap_merge` function merges the two heaps into one heap.
 *
 * @param h1, h2: the given nodes of two heaps
 *
 * The function makes sure that the new heap has its value as the minimum value of two original heaps.
 */
/*@
requires heap(h1, ?min1) &*& heap(h2, ?min2);
ensures heap(result, ?minResult) &*& minResult == (min1 < min2 ? min1 : min2);
@*/
struct heap_node *heap_merge(struct heap_node *h1, struct heap_node *h2)
{
    if (h1 == 0 && h2 == 0) {
        return h2;
    } else if (h1 == 0) {
        return h2;
    } else if (h2 == 0) {
        return h1;
    }

    struct heap_node *smaller;
    int smaller_val;

    if (h1->value <= h2->value) {
        smaller = h1;
        smaller_val = h1->value;

        struct heap_node *merged_right = heap_merge(h1->right, h2);
        smaller->right = merged_right;
    } else {
        smaller = h2;
        smaller_val = h2->value;

        struct heap_node *merged_right = heap_merge(h1, h2->right);
        smaller->right = merged_right;
    }

    return smaller;
}