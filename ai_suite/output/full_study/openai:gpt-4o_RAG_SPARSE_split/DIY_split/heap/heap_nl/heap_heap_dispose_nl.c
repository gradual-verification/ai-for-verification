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
predicate heap(struct heap_node *node) =
    node == 0 ? true :
    node->value |-> _ &*& node->left |-> ?left &*& node->right |-> ?right &*&
    malloc_block_heap_node(node) &*&
    heap(left) &*& heap(right);
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
    //@ requires heap(node);
    //@ ensures true;
{
    if (node != 0) {
        heap_dispose(node->left);
        heap_dispose(node->right);
        free(node);
    }
}