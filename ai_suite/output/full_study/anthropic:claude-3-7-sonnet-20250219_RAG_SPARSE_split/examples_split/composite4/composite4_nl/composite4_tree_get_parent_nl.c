#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate node_parent(struct node *n, struct node *p) = 
  n->parent |-> p;

predicate node(struct node *n) = 
  n->left |-> ?l &*& 
  n->right |-> ?r &*& 
  n->parent |-> ?p &*& 
  n->count |-> ?c &*&
  pointer_within_limits(n) == true;
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
//@ requires node != 0 &*& node(node);
//@ ensures node(node) &*& result == (struct node *)((char *)node_parent(node, ?p) ? p : 0);
{
  //@ open node(node);
  struct node *p = node->parent;
  //@ close node(node);
  return p;
}