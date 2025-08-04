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
// A predicate to describe a min-heap.
// It is defined recursively.
// A heap is either null (the base case) or a node with two sub-heaps.
// The predicate also tracks the minimum value of the heap.
predicate heap(struct heap_node *node; int min_val) =
    // An empty heap has a minimum value of INT_MAX.
    node == 0 ?
        min_val == INT_MAX
    :
        // A non-empty heap consists of a node...
        node->value |-> ?v &*&
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        malloc_block_heap_node(node) &*&
        // ...and two sub-heaps.
        heap(left, ?min_l) &*&
        heap(right, ?min_r) &*&
        // The min-heap property: the root is smaller than the minimums of its sub-heaps.
        v <= min_l &*& v <= min_r &*&
        // The minimum value of this heap is the value of the root node.
        min_val == v;
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `heap_dispose` function disposes a heap rooted at a given node.
 *
 * @param node: the heap_node as a root of a heap
 *
 * The function makes sure that the nodes in the heap are freed. 
 */
void heap_dispose(struct heap_node *node)
    //@ requires heap(node, _);
    //@ ensures true;
{
    if (node != 0) {
        //@ open heap(node, _);
        heap_dispose(node->left);
        heap_dispose(node->right);
        free(node);
    } else {
        //@ open heap(node, _);
    }
}