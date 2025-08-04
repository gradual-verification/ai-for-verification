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
    [_]result->childrenGhostListId |-> ?childrenGhostListId &*& ghost_list<struct node *>(childrenGhostListId, nil) &*&
    result->firstChild |-> 0 &*&
    result->nextSibling |-> next &*&
    result->parent |-> p &*&
    result->count |-> 1;
  @*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  //@ int id = create_ghost_list();
  //@ n->childrenGhostListId = id;
  //@ leak n->childrenGhostListId |-> id;
  return n;
}


struct node *create_tree()
  //@ requires true;
  //@ ensures tree(?id) &*& [_]tree_membership_fact(id, result);
{
  struct node *n = create_node(0, 0);
  //@ int id = create_ghost_list();
  //@ ghost_list_add(id, n);
  //@ open create_node(0, 0);
  //@ int childrenId = n->childrenGhostListId;
  //@ close children(0, nil);
  //@ close foreach2(nil, nil, child(id, n));
  //@ close node(id)(n);
  //@ close foreach(nil, node(id));
  //@ close tree(id);
  return n;
}


void add_to_count(struct node *p, int delta)
  /*@
  requires
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
  //@ open children(firstChild, children);
  //@ open foreach2(children, childrenCounts, child(id, p));
  struct node *pp = p->parent;
  if (p->count > INT_MAX - delta)
    abort();
  p->count += delta;
  //@ close node(id)(p);
  //@ foreach_unremove(p, nodes);
  if (pp == 0) {
    //@ leak tree_id(id);
  } else {
    //@ ghost_list_member_handle_lemma(id, pp);
    //@ foreach_remove(pp, nodes);
    //@ open node(id)(pp);
    //@ assert [_]pp->childrenGhostListId |-> ?ppChildrenId;
    //@ ghost_list_member_handle_lemma(ppChildrenId, p);
    //@ foreach2_remove(p, pp->firstChild, child(id, pp));
    //@ open child(id, pp)(p, _);
    //@ p->parent;
    //@ close child(id, pp)(p, 1 + sum(childrenCounts));
    //@ foreach2_unremove(p, pp->firstChild, child(id, pp));
    //@ close node(id)(pp);
    //@ foreach_unremove(pp, nodes);
    add_to_count(pp, delta);
  }
}


struct node *tree_add(struct node *node)
  //@ requires tree(?id) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id) &*& [_]tree_membership_fact(id, result);
{
  //@ open tree(id);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ foreach_remove(node, ?nodes);
  //@ open node(id)(node);
  //@ assert [_]node->childrenGhostListId |-> ?childrenId;
  
  struct node *n = create_node(node, node->firstChild);
  //@ ghost_list_add(id, n);
  //@ ghost_list_add(childrenId, n);
  
  node->firstChild = n;
  
  //@ open create_node(node, _);
  //@ int nChildrenId = n->childrenGhostListId;
  //@ close children(0, nil);
  //@ close foreach2(nil, nil, child(id, n));
  //@ close node(id)(n);
  //@ foreach_unremove(n, remove(node, nodes));
  
  //@ close child(id, node)(n, 1);
  //@ open children(n->nextSibling, ?cs);
  //@ open foreach2(n->nextSibling, ?ccs, child(id, node));
  //@ close tree_id(id);
  add_to_count(node, 1);

  return n;
}


struct node *tree_get_parent(struct node *node)
  //@ requires tree(?id) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id) &*& (result == 0 ? true : [_]tree_membership_fact(id, result));
{
  //@ open tree(id);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ foreach_remove(node, ?nodes);
  //@ open node(id)(node);
  struct node *p = node->parent;
  //@ if (p != 0) { ghost_list_member_handle_lemma(id, p); }
  //@ close node(id)(node);
  //@ foreach_unremove(node, nodes);
  //@ close tree(id);
  return p;
}


// TODO: make this function pass the verification
int main0()
  //@ requires true;
  //@ ensures true;
{
  struct node *node = create_tree();
  //@ open tree(?id);
  //@ close tree_id(id);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ struct node *n0 = node;

  node = tree_add(node);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ struct node *n1 = node;

  node = tree_add(node);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ struct node *n2 = node;

  node = tree_get_parent(node);
  //@ open tree(id);
  //@ ghost_list_member_handle_lemma(id, n2);
  //@ foreach_remove(n2, ?nodes_n2);
  //@ open node(id)(n2);
  //@ close node(id)(n2);
  //@ foreach_unremove(n2, nodes_n2);
  //@ close tree(id);
  if (node == 0) abort();

  node = tree_add(node);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ struct node *n3 = node;

  node = tree_get_parent(node);
  //@ open tree(id);
  //@ ghost_list_member_handle_lemma(id, n3);
  //@ foreach_remove(n3, ?nodes_n3);
  //@ open node(id)(n3);
  //@ close node(id)(n3);
  //@ foreach_unremove(n3, nodes_n3);
  //@ close tree(id);
  if (node == 0) abort();

  node = tree_get_parent(node);
  //@ open tree(id);
  //@ ghost_list_member_handle_lemma(id, n1);
  //@ foreach_remove(n1, ?nodes_n1);
  //@ open node(id)(n1);
  //@ close node(id)(n1);
  //@ foreach_unremove(n1, nodes_n1);
  //@ close tree(id);
  if (node == 0) abort();
  
  //@ leak tree(id);
  //@ leak tree_id(id);
  return 0;
}