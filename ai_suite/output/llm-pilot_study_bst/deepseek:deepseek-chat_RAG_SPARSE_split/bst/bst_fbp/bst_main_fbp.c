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
    //@ close bst(0, INT_MIN, INT_MAX);
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
        //@ close bst(0, min, value);
        //@ close bst(0, value, max);
        //@ close bst(new_node, min, max);
        return new_node;
    } else {
        //@ open bst(node, min, max);
        if (value < node->value) {
            struct bst_node *left = node->left;
            //@ assert bst(left, min, node->value);
            //@ assert min < value && value < node->value;
            struct bst_node *new_left = bst_insert(left, value);
            node->left = new_left;
            //@ close bst(node, min, max);
        } else if (value > node->value) {
            struct bst_node *right = node->right;
            //@ assert bst(right, node->value, max);
            //@ assert node->value < value && value < max;
            struct bst_node *new_right = bst_insert(right, value);
            node->right = new_right;
            //@ close bst(node, min, max);
        } else {
            //@ close bst(node, min, max);
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
    } else {
        //@ open bst(node, min, max);
        if (node->value == value) {
            //@ close bst(node, min, max);
            return true;
        } else if (value < node->value) {
            bool result = bst_search(node->left, value);
            //@ close bst(node, min, max);
            return result;
        } else {
            bool result = bst_search(node->right, value);
            //@ close bst(node, min, max);
            return result;
        }
    }
}

void bst_traverse(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max);
{
    if (node == 0) {
    } else {
        //@ open bst(node, min, max);
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
        //@ close bst(node, min, max);
    }
}

void bst_dispose(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures true;
{
    if (node != 0) {
        //@ open bst(node, min, max);
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
    tree = bst_insert(tree, 10);
    tree = bst_insert(tree, 5);
    tree = bst_insert(tree, 15);
    tree = bst_insert(tree, 8);
    tree = bst_insert(tree, 12);

    bool found8 = bst_search(tree, 8);
    bool found20 = bst_search(tree, 20);

    bst_traverse(tree);

    bst_dispose(tree);
    return 0;
}