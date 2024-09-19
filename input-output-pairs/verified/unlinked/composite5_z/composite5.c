#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>
//@ #include "ghostlist.gh"

// Some general infrastructure; should be in the VeriFast Library.

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
  ensures foreach2<a, b>(remove(a, as), remove_assoc(a, as, bs), p) &*& p(a, assoc2(a, as, bs)) &*& length(bs) == length(as);

fixpoint list<b> update2<a, b>(a a, b b, list<a> as, list<b> bs);

lemma void foreach2_unremove<a, b>(list<a> as, list<b> bs, a a, b b);
  requires foreach2<a, b>(remove(a, as), remove_assoc(a, as, bs), ?p) &*& mem(a, as) == true &*& p(a, b) &*& length(bs) == length(as);
  ensures foreach2<a, b>(as, update2(a, b, as, bs), p);

fixpoint int sum(list<int> xs) {
  switch (xs) {
    case nil: return 0;
    case cons(x, xs0): return x + sum(xs0);
  }
}

lemma void sum_update2<a>(a a, int b, list<a> as, list<int> bs);
  requires length(bs) == length(as);
  ensures sum(update2(a, b, as, bs)) == sum(bs) + b - assoc2(a, as, bs);

lemma void neq_mem_remove<t>(t x1, t x2, list<t> xs)
  requires x1 != x2 &*& mem(x1, xs) == true;
  ensures mem(x1, remove(x2, xs)) == true;
{
  switch (xs) {
    case nil:
    case cons(x, xs0):
      if (x == x1 || x == x2) {
      } else {
        neq_mem_remove(x1, x2, xs0);
      }
  }
}

lemma void neq_mem_remove2<t>(t x1, t x2, list<t> xs);
  requires mem(x1, xs) == true;
  ensures mem(x1, remove(x2, xs)) == true;

lemma void remove_commut<t>(t x1, t x2, list<t> xs);
  requires true;
  ensures remove(x1, remove(x2, xs)) == remove(x2, remove(x1, xs));

lemma void foreach_unremove_update1<t>(t x, list<t> xs, predicate(t) p_weak);
    requires foreach(remove(x, xs), ?p) &*& mem(x, xs) == true &*& p_weak(x);
    ensures foreach(xs, p_weak);

lemma void foreach_unremove_update2<t>(t x, list<t> xs, predicate(t) p_strong);
    requires foreach(remove(x, xs), ?p) &*& mem(x, xs) == true &*& p_strong(x);
    ensures foreach(xs, p);

lemma void malloc_node_success(struct node *m, struct node *n);
  requires m != 0;
  ensures m->firstChild |-> ?fc &*& fc == n;
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
  [1/2]c->count |-> count &*&   // I have a 'lock' on my child's count.
  [_]ghost_list_member_handle(id, c) &*&   // My child is in the tree.
  [1/2]c->parent |-> parent;   // I am my child's parent.

predicate_ctor node(int id, int delta)(struct node *n) =
  n != 0 &*&
  [_]n->childrenGhostListId |-> ?childrenId &*&
  n->firstChild |-> ?firstChild &*&
  children(firstChild, ?children) &*&
  ghost_list(childrenId, children) &*&
  foreach2(children, ?childrenCounts, child(id, n)) &*&
  [1/2]n->count |-> ?cnt &*& cnt == 1 + sum(childrenCounts) &*& cnt + delta <= INT_MAX &*&
  [1/2]n->parent |-> ?parent &*&
  parent == 0 ?
    [1/2]n->parent |-> 0 &*& n->nextSibling |-> _ &*& [1/2]n->count |-> _
  :
    parent != n &*&
    [_]ghost_list_member_handle(id, parent) &*&   // My parent is in the tree.
    [_]parent->childrenGhostListId |-> ?parentChildrenId &*&
    [_]ghost_list_member_handle(parentChildrenId, n);   // I am in my parent's list of children.

predicate tree(int id, int delta) =
  ghost_list<struct node *>(id, ?children) &*& foreach(children, node(id, delta));

//predicate predsAreNode(int id, struct node *n, int delta) =
//  n == 0 ?
//    true
//  :
//    node(id, delta)(n) &*& predsAreNode(id, n->parent, delta);

predicate tree_membership_fact(int id, struct node *n) = ghost_list_member_handle(id, n);

// setting the bounds for the result of adding count in a brute-force way
lemma void count_bounded(struct node *n, int delta);
  requires [?f]n->count |-> ?cnt;
  ensures [f]n->count |-> cnt &*& cnt + delta < INT_MAX;
@*/

/* private */
struct node *create_node(struct node *p, struct node *next)
  //@ requires true;
  /*@
  ensures
    result != 0 &*&
    [_]result->childrenGhostListId |-> ?childrenGhostListId &*& ghost_list<struct node *>(childrenGhostListId, nil) &*&
    result->firstChild |-> 0 &*&
    result->nextSibling |-> next &*&
    result->parent |-> p &*&
    result->count |-> 1;
  @*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  //@ int childrenGhostListId = create_ghost_list();
  //@ n->childrenGhostListId = childrenGhostListId;
  //@ leak node_childrenGhostListId(n, childrenGhostListId);
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  //@ leak malloc_block_node(n);
  return n;
}

struct node *create_tree()
  //@ requires emp;
  //@ ensures tree(?id, 1) &*& [_]tree_membership_fact(id, result);
{
  struct node *n = create_node(0, 0);
  //@ int id = create_ghost_list();
  //@ ghost_list_add(id, n);
  //@ close children(0, nil);
  //@ close foreach2(nil, nil, child(id, n));
  //@ close node(id, 1)(n);
  //@ close foreach(nil, node(id, 1));
  //@ close foreach(cons(n, nil), node(id, 1));
  //@ close tree(id, 1);
  //@ close tree_membership_fact(id, n);
  //@ leak tree_membership_fact(id, n);
  return n;
}

//@ predicate tree_id(int id) = true;

/* private */
void add_to_count(struct node *p, struct node *first_child, int delta)
  /*@
  requires
    p != 0 &*& delta >= 0 &*&
    tree_id(?id) &*&
    ghost_list(id, ?nodes) &*& // All nodes satisfy the 'node(id)' predicate, except 'p'.
    [_]p->childrenGhostListId |-> ?childrenId &*&
    p->firstChild |-> ?firstChild &*& firstChild == first_child &*& node(id, 0)(firstChild) &*&
    mem(firstChild, nodes) == true &*& mem(p, remove(firstChild, nodes)) == true &*& //mem(p, nodes) == true &*&
    foreach(remove(p, remove(firstChild, nodes)), node(id, delta)) &*&
    children(firstChild, ?children) &*&
    ghost_list(childrenId, children) &*&
    foreach2(children, ?childrenCounts, child(id, p)) &*&
    [1/2]p->count |-> ?cnt &*& cnt == 1 + sum(childrenCounts) - delta &*& cnt + delta <= INT_MAX &*& // Here's the rub.
    [1/2]p->parent |-> ?parent &*&
    //mem(parent, remove(firstChild, nodes)) == true &*&
    //mem(parent, remove(p, remove(firstChild, nodes))) == true &*&
    parent == 0 ?
      [1/2]p->parent |-> 0 &*& p->nextSibling |-> _ &*& [1/2]p->count |-> _
    :
      parent != p &*&
      [_]ghost_list_member_handle(id, parent) &*&
      [_]parent->childrenGhostListId |-> ?parentChildrenId &*&
      [_]ghost_list_member_handle(parentChildrenId, p);
  @*/
  //@ ensures tree(id, 0);
{
  struct node *pp = p->parent;
  // @ count_bounded(p, delta);
  if (pp == 0) {
    p->count += delta;
    //@ close node(id, 0)(p);
    //@ foreach_unremove_update1(p, remove(firstChild, nodes), node(id, 0));
    //@ foreach_unremove(firstChild, nodes);
    //@ close tree(id, 0);
    //@ open tree_id(id);
  } else {
    //@ malloc_node_success(pp, p);
    //@ ghost_list_member_handle_lemma(id, parent);
    //@ neq_mem_remove2(parent, firstChild, nodes);
    //@ neq_mem_remove(parent, p, remove(firstChild, nodes));
    //@ foreach_remove(parent, remove(p, remove(firstChild, nodes)));
    //@ open node(id, delta)(parent);
    //@ assert [_]parent->childrenGhostListId |-> ?parentChildrenGhostListId;
    //@ ghost_list_member_handle_lemma(parentChildrenGhostListId, p);
    //@ assert ghost_list(parentChildrenGhostListId, ?parentChildren);
    //@ assert foreach2(parentChildren, ?parentChildrenCounts, _);
    //@ foreach2_remove(parentChildren, p);
    //@ open child(id, parent)(p, _);
    p->count += delta;
    //@ close node(id, 0)(p);
    //@ remove_commut(parent, p, remove(firstChild, nodes));
    //@ neq_mem_remove(p, parent, remove(firstChild, nodes));
    // @ foreach_unremove_update1(p, remove(parent, remove(firstChild, nodes)), node(id, 0));
    //@ assert [_]p->count |-> ?count;
    //@ close child(id, parent)(p, count);
    //@ foreach2_unremove(parentChildren, parentChildrenCounts, p, count);
    //@ sum_update2(p, count, parentChildren, parentChildrenCounts);

    add_to_count(pp, p, delta);
  }
}

struct node *tree_add(struct node *node)
  //@ requires tree(?id, 1) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id, 0) &*& [_]tree_membership_fact(id, result);
{
  //@ open tree(_, 1);
  //@ open tree_membership_fact(_, _);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ assert ghost_list(id, ?nodes);
  //@ foreach_remove(node, nodes);
  //@ open node(id, 1)(node);
  struct node *n = create_node(node, node->firstChild);
  node->firstChild = n;
  //@ close tree_id(id);
  //@ close children(n, _);
  //@ assert [_]node->childrenGhostListId |-> ?childrenGhostListId;
  //@ ghost_list_add(childrenGhostListId, n);
  //@ leak ghost_list_member_handle(childrenGhostListId, n);
  //@ ghost_list_add(id, n);
  //@ leak ghost_list_member_handle(id, n);
  //@ close child(id, node)(n, 1);
  //@ close children(0, nil);
  //@ close foreach2(nil, nil, child(id, n));
  //@ close node(id, 0)(n);
  // @ close foreach(cons(n, remove(node, nodes)), node(id, 1));
  //@ assert foreach2<struct node *, int>(?children, ?childrenCounts, child(id, node));
  //@ close foreach2(cons(n, children), cons(1, childrenCounts), child(id, node));
  add_to_count(node, n, 1);
  //@ assert [?f]ghost_list_member_handle(id, n);
  //@ close [f]tree_membership_fact(id, n);
  return n;
}

struct node *tree_get_parent(struct node *node)
  //@ requires tree(?id, 0) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id, 0) &*& (result == 0 ? true : [_]tree_membership_fact(id, result));
{
  //@ open tree(id, 0);
  //@ open tree_membership_fact(id, node);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ assert ghost_list(id, ?nodes);
  //@ foreach_remove(node, nodes);
  //@ open node(id, 0)(node);
  struct node *p = node->parent;
  //@ close node(id, 0)(node);
  //@ foreach_unremove(node, nodes);
  //@ close tree(id, 0);
  /*@
  if (p != 0) {
    assert [?f]ghost_list_member_handle(id, p);
    close [f]tree_membership_fact(id, p);
  }
  @*/
  return p;
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
  //@ leak tree(_, _);
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
    //@ leak tree(_, _);
    return 0;
}