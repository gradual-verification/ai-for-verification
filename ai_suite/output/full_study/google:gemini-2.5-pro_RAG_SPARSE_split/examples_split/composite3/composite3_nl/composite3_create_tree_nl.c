#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate tree(struct node *n, struct node *p, int size) =
    n == 0 ?
        size == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> size &*&
        malloc_block_node(n) &*&
        tree(l, n, ?lsize) &*&
        tree(r, n, ?rsize) &*&
        size == 1 + lsize + rsize;
@*/

// TODO: make this function pass the verification
/*create_tree function
-param: void
-description: The function creates a tree with one node and returns it.

It makes sure that the returned value is a tree with one node.
*/
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, 0, 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close tree(0, n, 0);
    //@ close tree(0, n, 0);
    //@ close tree(n, 0, 1);
    return n;
}