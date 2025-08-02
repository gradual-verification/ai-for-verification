#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// Define a predicate for a tree node
predicate tree(struct node *node; int depth) =
    node == 0 ?
        depth == 0
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> ?parent &*&
        node->count |-> ?count &*&
        malloc_block_node(node) &*&
        tree(left, ?leftDepth) &*&
        tree(right, ?rightDepth) &*&
        depth == 1 + (leftDepth > rightDepth ? leftDepth : rightDepth);
@*/

/***
 * Description:
The subtree_dispose function recursively frees all memory associated with the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree to be disposed.

Requires: The subtree rooted at `node` is valid.
Ensures: All memory associated with the subtree is freed.
*/
void subtree_dispose(struct node *node)
//@ requires tree(node, ?depth);
//@ ensures true;
{
  if (node != 0) {
    {
      struct node *left = node->left;
      //@ open tree(node, depth);
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      //@ assert node->right |-> right;
      subtree_dispose(right);
    }
    free(node);
  }
  //@ else open tree(node, depth);
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
//@ requires tree(node, ?depth);
//@ ensures true;
{
  subtree_dispose(node);
}