#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n; struct node *parent) =
    n == 0 ?
        true
    :
        n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> parent &*& n->count |-> _ &*&
        malloc_block_node(n) &*&
        node(left, n) &*& node(right, n);

@*/

// TODO: make this function pass the verification
/*tree_get_parent function
-param: struct node *node
-description: The function gets the parent of the
current node. It requires that before the call, the current node and its parent are non-null.
It makes sure that the returned value is the parent of the current node and the tree is not changed.
*/
/*@ 
requires node(node, ?parent) &*& node != 0 &*& parent != 0;
ensures node(node, parent) &*& result == parent;
@*/
struct node *tree_get_parent(struct node *node)
{
    struct node *parent = node->parent;
    return parent;
}