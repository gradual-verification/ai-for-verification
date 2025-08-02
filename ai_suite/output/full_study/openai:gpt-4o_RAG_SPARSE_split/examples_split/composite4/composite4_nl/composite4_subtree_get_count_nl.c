#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@

predicate subtree(struct node *node) =
  node == 0 ? true : 
  node->count |-> ?count &*& count >= 0 &*&
  node->left |-> ?left &*& node->right |-> ?right &*&
  node->parent |-> ?parent &*&
  subtree(left) &*& subtree(right);

@*/

// TODO: make this function pass the verification
/***
 * Description:
The subtree_get_count function retrieves the count of nodes in the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree.

Requires: The subtree rooted at `node` is valid.
Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
/*@
requires subtree(node);
ensures subtree(node) &*& result >= 0;
@*/
int subtree_get_count(struct node *node)
{
  int result = 0;
  if (node != 0) { result = node->count; }
  return result;
}