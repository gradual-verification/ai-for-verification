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

/* 
   Constructs a single-node heap.

   The freshly allocated node satisfies the heap predicate:
   – the sub-heaps are the empty heap (node == 0 ⇒ min == INT_MAX);
   – therefore INT_MAX is the minimal element of each sub-heap and
     the requested value is not larger than these minima;
   – finally we wrap everything in one heap node whose minimum equals
     the stored value.
*/
//@ ensures heap(result, val);
struct heap_node *heap_create(int val)
    //@ requires true;
    //@ ensures heap(result, val);
{
    struct heap_node *node = malloc(sizeof(struct heap_node));
    if (node == 0) abort();

    /* initialise the freshly allocated memory */
    node->value = val;
    node->left  = 0;
    node->right = 0;

    /* build the abstract heap predicate for the two empty children   */
    //@ close heap(0, INT_MAX);          // left  child
    //@ close heap(0, INT_MAX);          // right child

    /* turn the raw malloc block into a typed malloc_block predicate  */
    //@ close malloc_block_heap_node(node);

    /* prove val ≤ INT_MAX                                              */
    //@ integer_limits(&node->value);

    /* finally close the heap predicate for the new root node          */
    //@ close heap(node, val);

    return node;
}