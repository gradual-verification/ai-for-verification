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
// Define a predicate for a heap node
predicate heap_node(struct heap_node *node; int val, struct heap_node *l, struct heap_node *r) =
    node->value |-> val &*& 
    node->left |-> l &*& 
    node->right |-> r &*& 
    malloc_block_heap_node(node);

// Define a predicate for a valid min-heap
predicate min_heap(struct heap_node *node) =
    node == 0 ?
        true
    :
        heap_node(node, ?val, ?l, ?r) &*&
        min_heap(l) &*&
        min_heap(r) &*&
        (l == 0 ? true : l->value |-> ?lval &*& val <= lval) &*&
        (r == 0 ? true : r->value |-> ?rval &*& val <= rval);
@*/

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
//@ ensures min_heap(result) &*& heap_node(result, val, 0, 0);
{
    struct heap_node *node = malloc(sizeof(struct heap_node));
    if (node == 0) abort();
    node->value = val;
    node->left = 0;
    node->right = 0;
    //@ close heap_node(node, val, 0, 0);
    //@ close min_heap(0);
    //@ close min_heap(0);
    //@ close min_heap(node);
    return node;
}