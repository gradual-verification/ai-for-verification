#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@

predicate node(struct node *n; struct node *p, struct node *next, int count) =
    n->firstChild |-> 0 &*& n->nextSibling |-> next &*& n->parent |-> p &*& n->count |-> count &*& malloc_block_node(n);

@*/

// TODO: make this function pass the verification
/*create_node function
-param: struct node *p, struct node *next
-description: This function creates a new node with a specified parent and next sibling.
The node is initialized with an empty list of children and a count of 1.
It returns a pointer to the newly created node, which is properly initialized.
*/
struct node *create_node(struct node *p, struct node *next)
    //@ requires true;
    //@ ensures node(result, p, next, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  //@ close node(n, p, next, 1);
  return n;
}