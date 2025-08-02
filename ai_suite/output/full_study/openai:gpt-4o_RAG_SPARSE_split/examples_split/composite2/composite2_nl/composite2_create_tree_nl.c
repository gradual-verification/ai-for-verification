#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate tree(struct node *n) =
    n == 0 ?
        true
    :
        n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*& n->count |-> 1 &*&
        malloc_block_node(n) &*&
        tree(left) &*& tree(right);

@*/

// TODO: make this function pass the verification
/*`create_tree()` Function:
- Parameters: None.
- Description: This function creates a new tree.

It makes sure that the return value is a tree. */
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close tree(n);
    return n;
}