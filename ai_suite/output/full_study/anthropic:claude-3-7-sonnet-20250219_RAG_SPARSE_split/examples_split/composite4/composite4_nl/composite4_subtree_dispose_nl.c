#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// Define a recursive predicate for a binary tree
predicate tree(struct node *node) =
    node == 0 ?
        emp
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> ?parent &*&
        node->count |-> ?count &*&
        malloc_block_node(node) &*&
        tree(left) &*&
        tree(right);
@*/

/**
 * Description:
 * The subtree_dispose function recursively frees all memory associated with the subtree rooted at the specified node.
 *
 * @param `node` - a pointer to the root of the subtree to be disposed.
 *
 * Requires: The subtree rooted at `node` is valid.
 * Ensures: All memory associated with the subtree is freed.
 */
void subtree_dispose(struct node *node)
//@ requires tree(node);
//@ ensures emp;
{
  if (node != 0) {
    {
      struct node *left = node->left;
      //@ open tree(node);
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    free(node);
    //@ close emp;
  } else {
    //@ open tree(node);
  }
}