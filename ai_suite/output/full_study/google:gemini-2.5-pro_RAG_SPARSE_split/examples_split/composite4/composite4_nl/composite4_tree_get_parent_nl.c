#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// A predicate to describe a single, allocated node.
// 'n' is an input parameter (the pointer to the node).
// 'left', 'right', 'parent', and 'count' are output parameters, representing the values of the fields.
// The semicolon ';' makes this a "precise" predicate, allowing automatic merging of fractional permissions.
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    // Permissions for each field of the struct.
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    // Permission for the memory block of the node itself, required for 'free'.
    malloc_block_node(n);
@*/


// TODO: make this function pass the verification
/***
 * Description: 
The tree_get_parent function retrieves the parent node of the specified node in the tree.

@param `node` - a pointer to the current node.

Requires: 
  - `node` is not null. 
Ensures: Returns the parent node of `node` and ensures the tree structure is unchanged.
*/
struct node *tree_get_parent(struct node *node)
    //@ requires [?f]node(node, ?l, ?r, ?p, ?c);
    //@ ensures [f]node(node, l, r, p, c) &*& result == p;
{
  //@ open [f]node(node, l, r, p, c);
  struct node *p = node->parent;
  //@ close [f]node(node, l, r, p, c);
  return p;
}