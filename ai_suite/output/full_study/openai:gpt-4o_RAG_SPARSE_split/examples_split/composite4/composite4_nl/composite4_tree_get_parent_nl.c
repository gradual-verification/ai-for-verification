#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

//@ predicate node(struct node *n; struct node *parent) =
//@   n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> parent &*& n->count |-> _ &*& malloc_block_node(n) &*&
//@   (left == 0 ? true : node(left, n)) &*& (right == 0 ? true : node(right, n));

/***
 * Description: 
 * The tree_get_parent function retrieves the parent node of the specified node in the tree.
 *
 * @param `node` - a pointer to the current node.
 *
 * Requires: 
 *   - `node` is not null. 
 * Ensures: Returns the parent node of `node` and ensures the tree structure is unchanged.
 */
//@ requires node(node, ?parent);
//@ ensures node(node, parent) &*& result == parent;
struct node *tree_get_parent(struct node *node)
{
  struct node *p = node->parent;
  return p;
}