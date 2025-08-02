#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@
// Define a predicate for a binary search tree
predicate bst_node(struct bst_node *node, int min, int max) =
    node == 0 ?
        true
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->value |-> ?value &*&
        malloc_block_bst_node(node) &*&
        min < value &*& value < max &*&
        bst_node(left, min, value) &*&
        bst_node(right, value, max);
@*/

/***
 * Description:
 * The `bst_create` function creates an empty BST.
 *
 *
 * The function makes sure that the new node is the root of a BST. 
 */
struct bst_node *bst_create()
//@ requires true;
//@ ensures bst_node(result, INT_MIN, INT_MAX);
{
    //@ close bst_node(0, INT_MIN, INT_MAX);
    return 0;
}

/***
 * Description:
 * The `bst_insert` function inserts a value into the BST.
 *
 * @param node: the root of the BST
 * @param value: the value to be inserted
 * 
 * The function requires that the value is within the range of possible MAX and MIN value of BST,
 * and ensures that the returned node is still a root of a BST.
 */
struct bst_node *bst_insert(struct bst_node *node, int value)
//@ requires bst_node(node, ?min, ?max) &*& min < value &*& value < max;
//@ ensures bst_node(result, min, max);
{
    if (node == 0) {
        //@ open bst_node(node, min, max);
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        //@ close bst_node(0, min, value);
        //@ close bst_node(0, value, max);
        //@ close bst_node(new_node, min, max);
        return new_node;
    } else {
        //@ open bst_node(node, min, max);
        if (value < node->value) {
            node->left = bst_insert(node->left, value);
        } else if (value > node->value) {
            node->right = bst_insert(node->right, value);
        } else {   
            // Value already exists, do nothing
        }
        //@ close bst_node(node, min, max);
        return node;
    }
}

/***
 * Description:
 * The `bst_search` function searches a value in the given BST.
 *
 * @param node: the root of the BST
 * @param value: the value to be searched
 * 
 * The function makes sure that the BST is still valid after the search operation,
 */
bool bst_search(struct bst_node *node, int value)
//@ requires bst_node(node, ?min, ?max);
//@ ensures bst_node(node, min, max);
{
    if (node == 0) {
        //@ open bst_node(node, min, max);
        //@ close bst_node(node, min, max);
        return false;
    }
    else if (node->value == value) {
        //@ open bst_node(node, min, max);
        //@ close bst_node(node, min, max);
        return true;
    }
    else if (value < node->value) {
        //@ open bst_node(node, min, max);
        bool result = bst_search(node->left, value);
        //@ close bst_node(node, min, max);
        return result;
    }
    else {
        //@ open bst_node(node, min, max);
        bool result = bst_search(node->right, value);
        //@ close bst_node(node, min, max);
        return result;
    }
}

/***
 * Description:
 * The `bst_traverse` function traverses the subtree of a given node.
 *
 * @param node: the node to be traversed on, which is a root of a bst
 *
 * The function makes sure that the given node is still a root of a bst. 
 */
void bst_traverse(struct bst_node *node)
//@ requires bst_node(node, ?min, ?max);
//@ ensures bst_node(node, min, max);
{
    if (node == 0) {
        //@ open bst_node(node, min, max);
        //@ close bst_node(node, min, max);
    } else {
        //@ open bst_node(node, min, max);
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
        //@ close bst_node(node, min, max);
    }
}

/***
 * Description:
 * The `bst_dispose` function frees a given BST.
 *
 * @param node: the root of the BST
 * 
 * The function makes sure that the nodes in the BST are freed.
 */
void bst_dispose(struct bst_node *node)
//@ requires bst_node(node, ?min, ?max);
//@ ensures true;
{
    if (node != 0) {
        //@ open bst_node(node, min, max);
        bst_dispose(node->left);
        bst_dispose(node->right);
        free(node);
    } else {
        //@ open bst_node(node, min, max);
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of BST.
 */
int main()
//@ requires true;
//@ ensures true;
{
    struct bst_node *tree = bst_create();
    
    //@ assert bst_node(tree, INT_MIN, INT_MAX);
    tree = bst_insert(tree, 10);
    //@ assert bst_node(tree, INT_MIN, INT_MAX);
    tree = bst_insert(tree, 5);
    //@ assert bst_node(tree, INT_MIN, INT_MAX);
    tree = bst_insert(tree, 15);
    //@ assert bst_node(tree, INT_MIN, INT_MAX);
    tree = bst_insert(tree, 8);
    //@ assert bst_node(tree, INT_MIN, INT_MAX);
    tree = bst_insert(tree, 12);
    //@ assert bst_node(tree, INT_MIN, INT_MAX);

    bool found8 = bst_search(tree, 8);
    //@ assert bst_node(tree, INT_MIN, INT_MAX);
    bool found20 = bst_search(tree, 20);
    //@ assert bst_node(tree, INT_MIN, INT_MAX);

    bst_traverse(tree);
    //@ assert bst_node(tree, INT_MIN, INT_MAX);

    bst_dispose(tree);
    return 0;
}