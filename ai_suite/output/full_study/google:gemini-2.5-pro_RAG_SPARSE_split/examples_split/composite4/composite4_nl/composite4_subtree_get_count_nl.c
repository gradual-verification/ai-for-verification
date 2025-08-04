#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate subtree(struct node *n; int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> ?p &*&
        n->count |-> c &*&
        malloc_block_node(n) &*&
        subtree(l, ?lc) &*&
        subtree(r, ?rc) &*&
        c == 1 + lc + rc &*& c >= 1;
@*/


/***
 * Description:
The subtree_get_count function retrieves the count of nodes in the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree.

Requires: The subtree rooted at `node` is valid.
Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?c);
    //@ ensures subtree(node, c) &*& result == c &*& result >= 0;
{
  int result = 0;
  if (node != 0) {
    result = node->count;
  }
  return result;
}