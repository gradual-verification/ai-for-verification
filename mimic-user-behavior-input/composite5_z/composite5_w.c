
#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>
//@ #include "ghostlist.gh"

// Weaker Specifications: Simplified verification predicates and lemmas.

/*@

predicate foreach2<a, b>(list<a> as, list<b> bs, predicate(a, b) p) =
  switch (as) {
    case nil: return bs == nil;
    case cons(a, as0): return
      switch (bs) {
        case nil: return false;
        case cons(b, bs0): return
          p(a, b) &*& foreach2(as0, bs0, p);
      };
  };

fixpoint list<b> remove_assoc<a, b>(a a, list<a> as, list<b> bs);
fixpoint b assoc2<a, b>(a a, list<a> as, list<b> bs);

lemma void foreach2_remove<a, b>(list<a> as, a a);
  requires foreach2<a, b>(as, ?bs, ?p) &*& mem(a, as) == true;
  ensures foreach2<a, b>(remove(a, as), remove_assoc(a, as, bs), p);

fixpoint list<b> update2<a, b>(a a, b b, list<a> as, list<b> bs);

lemma void foreach2_unremove<a, b>(list<a> as, list<b> bs, a a, b b);
  requires foreach2<a, b>(remove(a, as), remove_assoc(a, as, bs), ?p) &*& mem(a, as) == true &*& p(a, b);
  ensures foreach2<a, b>(as, update2(a, b, as, bs), p);

fixpoint int sum(list<int> xs) {
  switch (xs) {
    case nil: return 0;
    case cons(x, xs0): return x + sum(xs0);
  }
}

lemma void sum_update2<a>(a a, int b, list<a> as, list<int> bs);
  requires true;
  ensures sum(update2(a, b, as, bs)) == sum(bs) + b - assoc2(a, as, bs);

lemma void neq_mem_remove<t>(t x1, t x2, list<t> xs)
  requires x1 != x2 &*& mem(x1, xs) == true;
  ensures mem(x1, remove(x2, xs)) == true;

lemma void remove_commut<t>(t x1, t x2, list<t> xs);
  requires true;
  ensures remove(x1, remove(x2, xs)) == remove(x2, remove(x1, xs));

@*/

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
  //@ requires emp;
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
  //@ requires emp;
  //@ ensures emp;
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
    //@ requires emp;
    //@ ensures emp;
{
    struct node *root = create_tree();
    struct node *left = tree_add(root);
    struct node *leftRight = tree_add(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    struct node *leftLeft = tree_add(left);
    struct node *leftRightRight = tree_add(leftRight);
    return 0;
}

