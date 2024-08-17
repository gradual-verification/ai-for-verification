
#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>
//@ #include "ghostlist.gh"




struct node {
  //@ int childrenGhostListId;
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@

predicate children(struct node *c, list<struct node *> children) =
  c == 0 ?
    children == nil
  :
    c->nextSibling |-> ?next &*&
    children(next, ?children0) &*&
    children == cons(c, children0);

predicate_ctor child(int id, struct node *parent)(struct node *c, int count) =
  [1/2]c->count |-> count &*&
  [1/2]c->parent |-> parent;

predicate_ctor node(int id)(struct node *n) =
  n != 0 &*&
  n->firstChild |-> ?firstChild &*&
  children(firstChild, ?children) &*&
  foreach2(children, ?childrenCounts, child(id, n)) &*&
  [1/2]n->count |-> 1 + sum(childrenCounts) &*&
  [1/2]n->parent |-> ?parent;

predicate tree(int id) =
  ghost_list<struct node *>(id, ?children) &*& foreach(children, node(id));

predicate tree_membership_fact(int id, struct node *n) = ghost_list_member_handle(id, n);

@*/


struct node *create_node(struct node *p, struct node *next)
  //@ requires true;
  //@ ensures result != 0;
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();

  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  return n;
}


struct node *create_tree()
  //@ requires true;
  //@ ensures tree(?id) &*& [_]tree_membership_fact(id, result);
{
  struct node *n = create_node(0, 0);

  return n;
}


void add_to_count(struct node *p, int delta)
  //@ requires tree(?id);
  //@ ensures tree(id);
{
  struct node *pp = p->parent;
  p->count += delta;
  if (pp != 0) {
    add_to_count(pp, delta);
  }
}


struct node *tree_add(struct node *node)
  //@ requires tree(?id);
  //@ ensures tree(id) &*& [_]tree_membership_fact(id, result);
{
  struct node *n = create_node(node, node->firstChild);
  node->firstChild = n;
  add_to_count(node, 1);
  return n;
}


struct node *tree_get_parent(struct node *node)
  //@ requires tree(?id);
  //@ ensures tree(id);
{
  return node->parent;
}


int main0()
  //@ requires true;
  //@ ensures true;
{
  struct node *node = create_tree();
  node = tree_add(node);
  node = tree_add(node);
  node = tree_get_parent(node);
  if (node == 0) abort();
  node = tree_add(node);
  node = tree_get_parent(node);
  if (node == 0) abort();
  node = tree_get_parent(node);
  if (node == 0) abort();
  return 0;
}


int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct node *root = create_tree();
    struct node *left = tree_add(root);
    struct node *leftRight = tree_add(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    struct node *leftLeft = tree_add(left);
    struct node *leftRightRight = tree_add(leftRight);
    return 0;
}

