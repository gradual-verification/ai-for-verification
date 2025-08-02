#include "stdlib.h"
#include "stdbool.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*& malloc_block_node(n);

@*/

// TODO: make this function pass the verification
/*tree_has_parent function
-param: struct node *node
-description: The function checks if the parent of the
current node is not null. It requires that before the call, the current node is non-null.

It makes sure that the tree is unchanged and the returned value is true if the parent is not null.
*/
/*@
requires node(node, ?left, ?right, ?parent, ?count);
ensures node(node, left, right, parent, count) &*& result == (parent != 0);
@*/
bool tree_has_parent(struct node *node)
{
    struct node *parent1 = node->parent;
    return parent1 != 0;
}