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

// TODO: make this function pass the verification
struct heap_node *heap_create(int val)
    //@ requires true;
    //@ ensures heap(result, val);
{
    struct heap_node *node = malloc(sizeof(struct heap_node));
    if (node == 0) abort();
    node->value = val;
    node->left = 0;
    node->right = 0;
    return node;
}

// TODO: make this function pass the verification
struct heap_node *heap_insert(struct heap_node *root, int val)
    //@ requires heap(root, ?min_val);
    //@ ensures heap(result, min_val);
{
    if (root == 0) {
        return heap_create(val);
    } else {
        if (val < root->value) {
            root->left = heap_insert(root->left, val);
        } else {
            root->right = heap_insert(root->right, val);
        }
        return root;
    }
}

// TODO: make this function pass the verification
void heap_destroy(struct heap_node *node)
    //@ requires heap(node, ?min_val);
    //@ ensures true;
{
    if (node != 0) {
        heap_destroy(node->left);
        heap_destroy(node->right);
        free(node);
    }
}

// TODO: make this function pass the verification
int heap_min(struct heap_node *node)
    //@ requires heap(node, ?min_val);
    //@ ensures result == min_val;
{
    if (node == 0) {
        return INT_MAX; // or some other sentinel value
    } else {
        return node->value;
    }
}