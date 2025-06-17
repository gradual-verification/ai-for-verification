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

struct heap_node *heap_create(int val)
    //@ requires true;
    //@ ensures heap(result, val);
{
    struct heap_node *node = malloc(sizeof(struct heap_node));
    if (node == 0) abort();
    node->value = val;
    node->left = 0;
    node->right = 0;
    //@ close heap(0, INT_MAX);
    //@ close heap(0, INT_MAX);
    //@ close heap(node, val);
    return node;
}

struct heap_node *heap_merge(struct heap_node *h1, struct heap_node *h2)
    //@ requires heap(h1, ?min1) &*& heap(h2, ?min2);
    //@ ensures heap(result, ?new_min) &*& new_min == (min1 < min2 ? min1 : min2);
{
    if (h1 == 0 && h2 == 0) {
        //@ open heap(h1, min1);
        //@ open heap(h2, min2);
        //@ close heap(h2, min2);
        return h2;
    } else if (h1 == 0) {
        //@ open heap(h1, min1);
        //@ open heap(h2, min2);
        //@ close heap(h2, min2);
        return h2;
    } else if (h2 == 0) {
        //@ open heap(h2, min2);
        //@ open heap(h1, min1);
        //@ close heap(h1, min1);
        return h1;
    }

    //@ open heap(h1, min1);
    //@ open heap(h2, min2);
    struct heap_node *smaller;
    int smaller_val;

    if (h1->value <= h2->value) {
        smaller = h1;
        smaller_val = h1->value;

        //@ close heap(h2, min2);
        struct heap_node *merged_right = heap_merge(h1->right, h2);
        smaller->right = merged_right;
        //@ close heap(smaller, smaller_val);
    } else {
        smaller = h2;
        smaller_val = h2->value;

        //@ close heap(h1, min1);
        struct heap_node *merged_right = heap_merge(h1, h2->right);
        smaller->right = merged_right;
        //@ close heap(smaller, smaller_val);
    }

    return smaller;
}

int heap_get_min(struct heap_node *h)
    //@ requires heap(h, ?min_val) &*& h != 0;
    //@ ensures heap(h, min_val) &*& result == min_val;
{
    //@ open heap(h, min_val);
    int val = h->value;
    //@ close heap(h, min_val);
    return val;
}

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
