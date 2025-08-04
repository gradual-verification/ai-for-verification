#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Predicate describing a single node in memory.
// It takes the node pointer 'n' and logical variables for its fields.
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    // The pointer 'n' must be non-null.
    n != 0 &*&
    // The predicate grants ownership of the fields of the struct 'n'.
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    // This chunk indicates that 'n' points to a valid, allocated memory block.
    malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*tree_get_left function
-param: struct node *node
-description: The function gets the left node of the
current node. It requires that before the call, the current node and its left child are non-null.
It makes sure that the returned value is the left child of the current node and the tree is not changed.
*/
struct node *tree_get_left(struct node *node)
    /*@
    requires
        // The caller must provide ownership of 'node' and its fields.
        // The logical variables l, r, p, c capture the initial state.
        node(node, ?l, ?r, ?p, ?c) &*&
        // The left child must not be null, as per the description.
        l != 0;
    ensures
        // The function returns ownership of 'node' with its fields unchanged.
        node(node, l, r, p, c) &*&
        // The returned value is the left child of the node.
        result == l;
    @*/
{
    // VeriFast automatically opens the 'node' predicate to access the 'left' field.
    struct node *left = node->left;
    // VeriFast automatically closes the 'node' predicate before the function returns,
    // satisfying the 'ensures' clause.
    return left;
}