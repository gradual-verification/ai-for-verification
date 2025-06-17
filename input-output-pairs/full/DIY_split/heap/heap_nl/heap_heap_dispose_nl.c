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
 * The `heap_dispose` function disposes a heap rooted at a given node.
 *
 * @param node: the heap_node as a root of a heap
 *
 * The function makes sure that the nodes in the heap are freed. 
 */
void heap_dispose(struct heap_node *node)
{
    if (node != 0) {
        heap_dispose(node->left);
        heap_dispose(node->right);
        free(node);
    } else {
    }
}
