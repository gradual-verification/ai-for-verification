#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a tree node
predicate tree_node(struct node *node) =
    node != 0 &*&
    node->left |-> ?left &*&
    node->right |-> ?right &*&
    node->parent |-> ?parent &*&
    node->count |-> ?count &*&
    malloc_block_node(node);
@*/

// TODO: make this function pass the verification
/*tree_has_parent function
-param: struct node *node
-description: The function checks if the parent of the
current node is not null. It requires that before the call, the current node is non-null.

It makes sure that the tree is unchanged and the returned value is true if the parent is not null.
*/
bool tree_has_parent(struct node *node)
    //@ requires tree_node(node);
    //@ ensures tree_node(node) &*& result == (node->parent != 0);
{
    //@ open tree_node(node);
    struct node *parent1 = node->parent;
    //@ close tree_node(node);
    return parent1 != 0;
}