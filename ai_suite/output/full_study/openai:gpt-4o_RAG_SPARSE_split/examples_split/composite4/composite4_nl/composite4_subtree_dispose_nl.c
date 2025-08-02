#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate tree(struct node *n) =
    n == 0 ? true :
    n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*&
    n->count |-> _ &*& malloc_block_node(n) &*&
    tree(left) &*& tree(right);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The subtree_dispose function recursively frees all memory associated with the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree to be disposed.

Requires: The subtree rooted at `node` is valid.
Ensures: All memory associated with the subtree is freed.
*/
void subtree_dispose(struct node *node)
    //@ requires tree(node);
    //@ ensures true;
{
  if (node != 0) {
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    //@ open tree(node);
    free(node);
  }
}