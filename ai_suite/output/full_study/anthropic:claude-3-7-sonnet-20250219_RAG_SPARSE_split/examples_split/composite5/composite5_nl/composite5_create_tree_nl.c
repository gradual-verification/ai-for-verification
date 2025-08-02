#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@
// Define a predicate for a node
predicate node_pred(struct node *n; struct node *p, int c) =
  n->firstChild |-> ?fc &*&
  n->nextSibling |-> ?ns &*&
  n->parent |-> p &*&
  n->count |-> c &*&
  malloc_block_node(n);
@*/

/*create_node function
-param: struct node *p, struct node *next
-description: This function creates a new node with a specified parent and next sibling.
The node is initialized with an empty list of children and a count of 1.
It returns a pointer to the newly created node, which is properly initialized.
*/
struct node *create_node(struct node *p, struct node *next)
//@ requires true;
//@ ensures node_pred(result, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  //@ close node_pred(n, p, 1);
  return n;
}

/*create_tree function
-param: none
-description: This function creates a new tree.
It returns a pointer to the root node of the newly created tree. 
The tree is properly initialized with the root node as the only node.
*/
struct node *create_tree()
//@ requires true;
//@ ensures node_pred(result, 0, 1);
{
  struct node *n = create_node(0, 0);
  return n;
}