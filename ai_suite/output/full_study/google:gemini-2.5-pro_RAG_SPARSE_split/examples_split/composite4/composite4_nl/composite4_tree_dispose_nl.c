#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate tree(struct node *n) =
    n == 0 ?
        emp
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> ?p &*&
        n->count |-> ?c &*&
        malloc_block_node(n) &*&
        tree(l) &*&
        tree(r);
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
    //@ ensures emp;
{
  //@ open tree(node);
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
    //@ ensures emp;
{
  subtree_dispose(node);
}