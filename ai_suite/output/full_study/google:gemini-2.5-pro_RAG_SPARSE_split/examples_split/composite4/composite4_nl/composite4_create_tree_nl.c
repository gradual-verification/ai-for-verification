#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// A predicate to represent a well-formed tree.
// 'n' is the root of the tree/subtree.
// 'p' is the parent of the root 'n'.
// 'count' is the total number of nodes in the tree/subtree.
predicate tree(struct node *n, struct node *p; int count) =
    n == 0 ?
        // An empty tree has 0 nodes.
        count == 0
    :
        // A non-empty tree has a root node 'n'.
        // We must own the memory for the node and its fields.
        n->parent |-> p &*&
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->count |-> count &*&
        malloc_block_node(n) &*&
        // The left and right children must be well-formed trees.
        tree(l, n, ?lcount) &*&
        tree(r, n, ?rcount) &*&
        // The count of the current node must be 1 (for itself) plus the counts
        // of its left and right subtrees.
        count == 1 + lcount + rcount;
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
    //@ ensures tree(result, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close tree(0, n, 0); // The left child is an empty tree.
  //@ close tree(0, n, 0); // The right child is an empty tree.
  //@ close tree(n, p, 1); // Close the predicate for the newly created node.
  return n;
}


// TODO: make this function pass the verification
/***
 * Description: 
The create_tree function creates a new tree with a single root node.

@param None.

Requires: No specific preconditions.
Ensures: Returns a pointer to the root node of the newly created tree.
*/
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, 0, 1);
{
  // A tree is created by making a single node with no parent (parent is NULL/0).
  struct node *n = create_node(0);
  return n;
}