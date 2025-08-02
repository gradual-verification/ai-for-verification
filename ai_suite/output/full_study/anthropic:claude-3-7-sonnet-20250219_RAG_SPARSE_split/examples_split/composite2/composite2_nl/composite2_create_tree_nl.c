#include "stdlib.h"

/*@
predicate tree(struct node *t; int count) =
    t == 0 ?
        count == 0
    :
        t->left |-> ?left &*& t->right |-> ?right &*& t->parent |-> ?parent &*& t->count |-> ?c &*&
        malloc_block_node(t) &*& tree(left, ?lcount) &*& tree(right, ?rcount) &*&
        count == lcount + rcount + 1;
@*/

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



// TODO: make this function pass the verification
/*`create_tree()` Function:
- Parameters: None.
- Description: This function creates a new tree.

It makes sure that the return value is a tree. */
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close tree(0, 0);
    //@ close tree(0, 0);
    //@ close tree(n, 1);
    return n;
}