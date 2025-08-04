#include "stdlib.h"
//@ #include "ghostlist.gh"


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

fixpoint int sum(list<int> xs) {
  switch (xs) {
    case nil: return 0;
    case cons(x, xs0): return x + sum(xs0);
  }
}
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

predicate_ctor node(int id)(struct node *n) =
  n != 0 &*&
  [_]n->childrenGhostListId |-> ?childrenId &*&
  n->firstChild |-> ?firstChild &*&
  children(firstChild, ?children) &*&
  ghost_list(childrenId, children) &*&
  foreach2(children, ?childrenCounts, child(id, n)) &*&
  [1/2]n->count |-> 1 + sum(childrenCounts) &*&
  [1/2]n->parent |-> ?parent &*&
  parent == 0 ?
    [1/2]n->parent |-> 0 &*& n->nextSibling |-> _ &*& [1/2]n->count |-> _
  :
    parent != n &*&
    [_]ghost_list_member_handle(id, parent) &*&   // My parent is in the tree.
    [_]parent->childrenGhostListId |-> ?parentChildrenId &*&
    [_]ghost_list_member_handle(parentChildrenId, n);   // I am in my parent's list of children.

predicate tree(int id) =
  ghost_list<struct node *>(id, ?children) &*& foreach(children, node(id));

predicate tree_membership_fact(int id, struct node *n) = ghost_list_member_handle(id, n);
@*/

//@ predicate tree_id(int id) = true;


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
  //@ int childrenGhostListId = create_ghost_list<struct node*>();
  //@ n->childrenGhostListId = childrenGhostListId;
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  return n;
}


void add_to_count(struct node *p, int delta)
  /*@
  requires
    p != 0 &*&
    tree_id(?id) &*&
    ghost_list(id, ?nodes) &*& mem(p, nodes) == true &*& foreach(remove(p, nodes), node(id)) &*&   // All nodes satisfy the 'node(id)' predicate, except 'p'.
    [_]p->childrenGhostListId |-> ?childrenId &*&
    p->firstChild |-> ?firstChild &*&
    children(firstChild, ?children) &*&
    ghost_list(childrenId, children) &*&
    foreach2(children, ?childrenCounts, child(id, p)) &*& delta > 0 &*&
    [1/2]p->count |-> 1 + sum(childrenCounts) - delta &*& // Here's the rub.
    [1/2]p->parent |-> ?parent &*&
    parent == 0 ?
      [1/2]p->parent |-> 0 &*& p->nextSibling |-> _ &*& [1/2]p->count |-> _
    :
      parent != p &*&
      [_]ghost_list_member_handle(id, parent) &*&
      [_]parent->childrenGhostListId |-> ?parentChildrenId &*&
      [_]ghost_list_member_handle(parentChildrenId, p);
  @*/
  //@ ensures tree(id);
{
  //@ open tree_id(id);
  struct node *pp = p->parent;
  if (p->count > INT_MAX - delta)
    abort();
  p->count += delta;
  //@ close node(id)(p);
  //@ foreach_unremove(p, nodes);
  if (pp == 0) {
    //@ close tree(id);
  } else {
    //@ ghost_list_member_handle_lemma(id, pp);
    //@ foreach_remove(pp, nodes);
    //@ open node(id)(pp);
    //@ assert [_]pp->childrenGhostListId |-> ?ppChildrenId &*& pp->firstChild |-> ?ppFirstChild &*& children(ppFirstChild, ?ppChildren) &*& ghost_list(ppChildrenId, ppChildren) &*& foreach2(ppChildren, ?ppChildrenCounts, child(id, pp));
    //@ int p_index = index_of(p, ppChildren);
    //@ list<int> new_ppChildrenCounts = update(p_index, 1 + sum(childrenCounts), ppChildrenCounts);
    //@ foreach2_remove(p, ppChildren);
    //@ open child(id, pp)(p, 1 + sum(childrenCounts) - delta);
    //@ close child(id, pp)(p, 1 + sum(childrenCounts));
    //@ foreach2_unremove(p, ppChildren, new_ppChildrenCounts);
    //@ sum_update(p_index, 1 + sum(childrenCounts), ppChildrenCounts);
    add_to_count(pp, delta);
  }
}


// TODO: make this function pass the verification
struct node *tree_add(struct node *node)
  //@ requires tree(?id) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id) &*& [_]tree_membership_fact(id, result);
{
    //@ open tree(id);
    //@ ghost_list_member_handle_lemma(id, node);
    //@ foreach_remove(node, nodes);
    //@ open node(id)(node);
    //@ assert [_]node->childrenGhostListId |-> ?childrenId &*& node->firstChild |-> ?firstChild &*& children(firstChild, ?children) &*& ghost_list(childrenId, children) &*& foreach2(children, ?childrenCounts, child(id, node));

    struct node *n = create_node(node, node->firstChild);
    //@ assert n != 0 &*& [_]n->childrenGhostListId |-> ?nChildrenId &*& ghost_list(nChildrenId, nil) &*& n->firstChild |-> 0 &*& n->nextSibling |-> firstChild &*& n->parent |-> node &*& n->count |-> 1;

    node->firstChild = n;
    //@ close children(n, cons(n, children));

    // Add the new node 'n' to the tree's main ghost list.
    //@ ghost_list_add(id, n);
    //@ assert ghost_list_member_handle(id, n);

    // Add 'n' to its parent's children ghost list.
    //@ ghost_list_add(childrenId, n);
    //@ ghost_list_member_handle_lemma(childrenId, n);

    // Construct the 'child' predicate for the new node 'n'.
    //@ close [1/2]n->count |-> 1;
    //@ close [1/2]n->parent |-> node;
    //@ close child(id, node)(n, 1);

    // Construct the 'node' predicate for the new node 'n'.
    //@ close children(0, nil);
    //@ close foreach2(nil, nil, child(id, n));
    //@ close [1/2]n->count |-> 1;
    //@ close [1/2]n->parent |-> node;
    //@ close node(id)(n);

    // Now, assemble the arguments for add_to_count.
    // The list of all nodes is now 'cons(n, nodes)'.
    // The list of nodes to check in foreach is 'remove(node, cons(n, nodes))' which is 'cons(n, remove(node, nodes))'.
    //@ close foreach(cons(n, remove(node, nodes)), node(id));

    // The list of children of 'node' is now 'cons(n, children)'.
    // The list of children counts is 'cons(1, childrenCounts)'.
    //@ close foreach2(cons(n, children), cons(1, childrenCounts), child(id, node));

    //@ close tree_id(id);
    add_to_count(node, 1);

    //@ close tree_membership_fact(id, n);
    return n;
}