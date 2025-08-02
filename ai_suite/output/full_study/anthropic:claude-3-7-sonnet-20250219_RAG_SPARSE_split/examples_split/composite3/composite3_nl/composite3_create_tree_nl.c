#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a tree node
predicate tree_node(struct node *n) =
    n != 0 &*&
    n->left |-> ?left &*&
    n->right |-> ?right &*&
    n->parent |-> ?parent &*&
    n->count |-> ?count &*&
    malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*create_tree function
-param: void
-description: The function creates a tree with one node and returns it.

It makes sure that the returned value is a tree with one node.
*/
struct node *create_tree()
//@ requires true;
//@ ensures tree_node(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close tree_node(n);
    return n;
}