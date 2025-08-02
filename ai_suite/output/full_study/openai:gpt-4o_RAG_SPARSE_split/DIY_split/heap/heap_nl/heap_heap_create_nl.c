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
predicate heap_node(struct heap_node *node, int val) =
    node->value |-> val &*& node->left |-> 0 &*& node->right |-> 0 &*& malloc_block_heap_node(node);
@*/

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
    //@ requires true;
    //@ ensures result != 0 ? heap_node(result, val) : true;
{
    struct heap_node *node = malloc(sizeof(struct heap_node));
    if (node == 0) abort();
    node->value = val;
    node->left = 0;
    node->right = 0;
    //@ close heap_node(node, val);
    return node;
}