#include "stdlib.h"
#include "limits.h"

struct heap_node {
    int value;
    struct heap_node *left;
    struct heap_node *right;
};

/*@
predicate malloc_block_heap_node(struct heap_node *node) = malloc_block(node, sizeof(struct heap_node));

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

void heap_dispose(struct heap_node *node)
    //@ requires heap(node, _);
    //@ ensures true;
{
    if (node != 0) {
        //@ open heap(node, _);
        heap_dispose(node->left);
        heap_dispose(node->right);
        //@ close_struct(node); // Combine fields into chars_ chunk
        free(node);
    } else {
        //@ open heap(node, _);
    }
}