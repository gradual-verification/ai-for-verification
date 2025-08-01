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
 * The `heap_create` function creates a single heap node with the given value.
 *
 * @param val: the value in the new heap node
 *
 * The function makes sure that the new node is the root of a heap with its value as val.
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
