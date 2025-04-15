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

/***
 * Description:
 * The `heap_create` function creates a single heap node with the given value.
 *
 * @param val: the value in the new heap node
 *
 * The function allocates memory for a new `heap_node`, sets its value, 
 * and sets its left and right child as 0.
 * It makes sure that the new node is the root of a heap. 
 */
struct heap_node *heap_create(int val)
{
    struct heap_node *node = malloc(sizeof(struct heap_node));
    if (node == 0) abort();
    node->value = val;
    node->left = 0;
    node->right = 0;
    return node;
}

/***
 * Description:
 * The `heap_merge` function merges the two heaps into one heap.
 *
 * @param h1, h2: the given nodes of two heaps that have the heap property.
 *
 * The function lets the new root have the smallest value, and then recursively merge the heaps. 
 * It makes sure that the new heap maintains the heap property and its root value is the minimum of two original heaps.
 */
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

/***
 * Description:
 * The `heap_get_min` function gets the minimum value of a given heap.
 *
 * @param h1, h2: the given node of a heap that is not null and has the heap property
 *
 * It makes sure that the heap property is still perserved and the return value is the minimum value of the heap. 
 */
int heap_get_min(struct heap_node *h)
{
    int val = h->value;
    return val;
}

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
