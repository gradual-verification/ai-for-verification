#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@

predicate node(struct node *n; struct node *parent, int count) =
  n->firstChild |-> ?firstChild &*&
  n->nextSibling |-> ?nextSibling &*&
  n->parent |-> parent &*&
  n->count |-> count &*&
  malloc_block_node(n) &*&
  (firstChild == 0 ? true : node(firstChild, n, ?childCount)) &*&
  (nextSibling == 0 ? true : node(nextSibling, parent, ?siblingCount)) &*&
  count == (firstChild == 0 ? 1 : childCount + 1) + (nextSibling == 0 ? 0 : siblingCount);

predicate tree(struct node *root) =
  root == 0 ? true : node(root, 0, _);

@*/

// TODO: make this function pass the verification
void add_to_count(struct node *p, int delta)
  //@ requires p != 0 &*& tree(p) &*& delta > 0;
  //@ ensures tree(p);
{
  struct node *pp = p->parent;
 
  if (pp == 0) {
    p->count += delta;
  } else {
    p->count += delta;
    add_to_count(pp, delta);
  }
}