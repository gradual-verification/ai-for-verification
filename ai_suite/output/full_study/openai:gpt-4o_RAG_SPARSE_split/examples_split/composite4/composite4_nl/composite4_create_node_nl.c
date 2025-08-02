#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

//@ predicate node(struct node *n; struct node *p) =
//@   n->left |-> 0 &*& n->right |-> 0 &*& n->parent |-> p &*& n->count |-> 1 &*& malloc_block_node(n);

// TODO: make this function pass the verification
/***
* Description:
The create_node function creates a new node in the tree with the specified parent node, and initializes its left and right children as empty.

@param `p` - a pointer to the parent node.

Requires: No specific preconditions.
Ensures: Returns a pointer to the newly created node, and the subtree rooted at this node is correctly initialized.
*/
struct node * create_node(struct node * p)
  //@ requires true;
  //@ ensures node(result, p);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close node(n, p);
  return n;
}