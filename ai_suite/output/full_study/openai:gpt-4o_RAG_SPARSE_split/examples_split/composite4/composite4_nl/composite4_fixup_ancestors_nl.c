#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*& malloc_block_node(n);

predicate subtree(struct node *n; int count) =
  n == 0 ? count == 0 : node(n, ?left, ?right, ?parent, count) &*& subtree(left, ?leftCount) &*& subtree(right, ?rightCount) &*& count == 1 + leftCount + rightCount;

predicate ancestors(struct node *n, struct node *p) =
  n == 0 ? p == 0 : node(n, ?left, ?right, p, ?count) &*& ancestors(p, ?pp);

@*/

/***
 * Description:
The subtree_get_count function retrieves the count of nodes in the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree.

Requires: The subtree rooted at `node` is valid.
Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?count);
  //@ ensures subtree(node, count) &*& result == count;
{
  int result = 0;
  if (node != 0) { result = node->count; }
  return result;
}

// TODO: make this function pass the verification
/***
 * Description:
The fixup_ancestors function updates the count of nodes in the subtree for all ancestor nodes starting from the specified node.

@param `n` - a pointer to the current node.
@param `p` - a pointer to the parent node.
@param `count` - the updated count of nodes in the subtree rooted at the current node.

Requires: The parent node is the parent of the current node, and the count is non-negative.
Ensures: The ancestor nodes are updated with the correct count.
*/
void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires ancestors(n, p) &*& count >= 0;
  //@ ensures ancestors(n, p);
{
  if (p == 0) {
    //@ open ancestors(n, p);
    //@ close ancestors(n, p);
  } else {
    //@ open ancestors(n, p);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close ancestors(n, p);
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}