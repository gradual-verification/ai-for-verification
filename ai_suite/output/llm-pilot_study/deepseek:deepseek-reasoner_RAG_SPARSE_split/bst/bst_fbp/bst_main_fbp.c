#include "stdlib.h"
#include "stdbool.h"

struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@ 
predicate bst(struct bst_node *node, int min, int max) =
    node == 0 ?
        true
    :
        malloc_block_bst_node(node) &*&
        node->value |-> ?v &*& min < v &*& v < max &*&
        node->left |-> ?left &*& node->right |-> ?right &*&
        bst(left, min, v) &*& bst(right, v, max);
@*/

struct bst_node *bst_create()
    //@ requires true;
    //@ ensures bst(result, INT_MIN, INT_MAX);
{
    return 0;
}

struct bst_node *bst_insert(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max) &*& min < value &*& value < max;
    //@ ensures bst(result, min, max);
{
    if (node == 0) {
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        return new_node;
    } else {
        if (value < node->value) {
            node->left = bst_insert(node->left, value);
        } else if (value > node->value) {
            node->right = bst_insert(node->right, value);
        } else {   
        }
        return node;
    }
}

bool bst_search(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max);
{
    if (node == 0) {
        return false;
    }
    else if (node->value == value) {
        return true;
    }
    else if (value < node->value) {
        return bst_search(node->left, value);
    }
    else {
        return bst_search(node->right, value);
    }
}

void bst_traverse(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max);
{
    if (node == 0) {
    } else {
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
    }
}

void bst_dispose(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures true;
{
    if (node != 0) {
        bst_dispose(node->left);
        bst_dispose(node->right);
        free(node);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct bst_node *tree = bst_create();
    //@ assert bst(tree, INT_MIN, INT_MAX);
    
    tree = bst_insert(tree, 10);
    //@ assert bst(tree, INT_MIN, INT_MAX);
    
    tree = bst_insert(tree, 5);
    //@ assert bst(tree, INT_MIN, INT_MAX);
    
    tree = bst_insert(tree, 15);
    //@ assert bst(tree, INT_MIN, INT_MAX);
    
    tree = bst_insert(tree, 8);
    //@ assert bst(tree, INT_MIN, INT_MAX);
    
    tree = bst_insert(tree, 12);
    //@ assert bst(tree, INT_MIN, INT_MAX);

    bool found8 = bst_search(tree, 8);
    bool found20 = bst_search(tree, 20);

    bst_traverse(tree);  // Fixed function name

    bst_dispose(tree);
    return 0;
}