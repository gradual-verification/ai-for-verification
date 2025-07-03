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
        //@ close bst(0, min, value);
        //@ close bst(0, value, max);
        //@ close bst(new_node, min, max);
        return new_node;
    } else {
        if (value < node->value) {
            struct bst_node *left = node->left;
            //@ open bst(left, min, node->value);
            node->left = bst_insert(left, value);
            //@ close bst(node->left, min, node->value);
        } else if (value > node->value) {
            struct bst_node *right = node->right;
            //@ open bst(right, node->value, max);
            node->right = bst_insert(right, value);
            //@ close bst(node->right, node->value, max);
        }
        //@ close bst(node, min, max);
        return node;
    }
}

bool bst_search(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max) &*& result == (min < value && value < max && (node != 0 ==> (
    //@     node->value == value || (value < node->value ? bst_search(node->left, value) : bst_search(node->right, value))));
{
    if (node == 0) {
        return false;
    }
    else if (node->value == value) {
        return true;
    }
    else if (value < node->value) {
        bool result = bst_search(node->left, value);
        return result;
    }
    else {
        bool result = bst_search(node->right, value);
        return result;
    }
}

void bst_traverse(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures bst(node, min, max);
{
    if (node == 0) {
    } else {
        int val = node->value;
        //@ open bst(node->left, min, val);
        bst_traverse(node->left);
        //@ close bst(node->left, min, val);
        //@ open bst(node->right, val, max);
        bst_traverse(node->right);
        //@ close bst(node->right, val, max);
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