#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// Define a predicate for a valid binary tree node
predicate tree_node(struct node *n) =
    n == 0 ?
        true
    :
        n->left |-> ?left &*&
        n->right |-> ?right &*&
        n->parent |-> ?parent &*&
        n->count |-> ?count &*&
        count >= 0 &*&
        malloc_block_node(n) &*&
        tree_node(left) &*&
        tree_node(right);
@*/

/***
 * Description:
The subtree_get_count function retrieves the count of nodes in the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree.

Requires: The subtree rooted at `node` is valid.
Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
int subtree_get_count(struct node *node)
//@ requires tree_node(node);
//@ ensures tree_node(node) &*& result >= 0;
{
  int result = 0;
  //@ open tree_node(node);
  if (node != 0) { result = node->count; }
  //@ close tree_node(node);
  return result;
}