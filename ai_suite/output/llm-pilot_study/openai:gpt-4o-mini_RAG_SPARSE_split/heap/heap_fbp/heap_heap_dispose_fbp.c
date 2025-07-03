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
void heap_dispose(struct heap_node *node)
    //@ requires heap(node, _);
    //@ ensures true;
{
    if (node != 0) {
        heap_dispose(node->left);
        heap_dispose(node->right);
        free(node);
    } else {
    }
}

/*@
lemma void heap_dispose_lemma(struct heap_node *node)
    requires heap(node, ?min_val);
    ensures true;
{
    if (node != 0) {
        open heap(node, min_val);
        heap_dispose_lemma(node->left);
        heap_dispose_lemma(node->right);
        close heap(node, min_val);
    }
}
@*/

// The following function is used to verify the heap_dispose function
void test_heap_dispose()
    //@ requires true;
    //@ ensures true;
{
    struct heap_node *root = malloc(sizeof(struct heap_node));
    root->value = 10;
    root->left = malloc(sizeof(struct heap_node));
    root->left->value = 5;
    root->right = malloc(sizeof(struct heap_node));
    root->right->value = 15;

    //@ close heap(root, 10);
    heap_dispose(root);
}