#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// Define a predicate for a tree node
predicate tree_node(struct node *n, struct node *p) =
  n == 0 ?
    emp
  :
    n->left |-> ?l &*&
    n->right |-> ?r &*&
    n->parent |-> p &*&
    n->count |-> ?c &*&
    malloc_block_node(n) &*&
    tree_node(l, n) &*&
    tree_node(r, n);
@*/

/***
* Description:
The create_node function creates a new node in the tree with the specified parent node, and initializes its left and right children as empty.

@param `p` - a pointer to the parent node.

Requires: No specific preconditions.
Ensures: Returns a pointer to the newly created node, and the subtree rooted at this node is correctly initialized.
*/
struct node * create_node(struct node * p)
//@ requires true;
//@ ensures tree_node(result, p);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close tree_node(0, n);  // Close predicate for left child
  //@ close tree_node(0, n);  // Close predicate for right child
  //@ close tree_node(n, p);  // Close predicate for the new node
  return n;
}