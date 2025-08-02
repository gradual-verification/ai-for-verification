#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate tree(struct node *node;) =
  node == 0 ? true : 
  node->left |-> ?left &*& node->right |-> ?right &*& node->parent |-> ?parent &*& node->count |-> _ &*&
  malloc_block_node(node) &*& tree(left) &*& tree(right);
@*/

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
    free(node);
  }
}

// TODO: make this function pass the verification
/***
 * Description:
The tree_dispose function frees all memory associated with the tree rooted at the specified node.

@param `node` - a pointer to the root of the tree to be disposed.

Requires: The tree rooted at `node` is valid.
Ensures: All memory associated with the tree is freed.
*/
void tree_dispose(struct node *node)
  //@ requires tree(node);
  //@ ensures true;
{
  subtree_dispose(node);
}