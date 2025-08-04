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
  //@ int childrenId = create_ghost_list();
  //@ n->childrenGhostListId = childrenId;
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
  int id = create_ghost_list<struct node *>();
  struct node *n = create_node(0, 0);
  ghost_list_add(id, n);
  //@ open [_]n->childrenGhostListId |-> ?childrenId &*& ghost_list(childrenId, nil);
  //@ close children(0, nil);
  //@ close foreach2(nil, nil, child(id, n));
  //@ sum_nil();
  //@ close node(id)(n);
  //@ close foreach(cons(n, nil), node(id));
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
  struct node *pp = p->parent;
  if (p->count > INT_MAX - delta)
    abort();
  if (pp == 0) {
    p->count += delta;
    //@ close node(id)(p);
    //@ foreach_unremove(p, nodes);
    //@ close tree(id);
  } else {
    p->count += delta;
    //@ close node(id)(p);
    //@ foreach_unremove(p, nodes);
    //@ open tree(id);
    //@ assert ghost_list(id, ?nodes2) &*& foreach(nodes2, node(id));
    //@ ghost_list_member_handle_lemma(id, pp);
    //@ foreach_remove(pp, nodes2);
    //@ open node(id)(pp);
    //@ assert [_]pp->childrenGhostListId |-> ?ppChildrenId;
    //@ assert pp->firstChild |-> ?pp_fc;
    //@ assert children(pp_fc, ?pp_children);
    //@ assert ghost_list(ppChildrenId, pp_children);
    //@ assert foreach2(pp_children, ?pp_children_counts, child(id, pp));
    //@ assert [1/2]pp->count |-> 1 + sum(pp_children_counts);
    //@ assert [1/2]pp->parent |-> ?ppp;
    //@ foreach2_mem(p);
    //@ open foreach2_mem_results<struct node *, int>(?cs1, ?cs2, ?ccs1, ?p_count, ?ccs2);
    //@ open child(id, pp)(p, p_count);
    //@ close child(id, pp)(p, p_count + delta);
    //@ foreach2_append(cs1, cons(p, cs2));
    //@ sum_append(ccs1, cons(p_count, ccs2));
    //@ sum_append(ccs1, cons(p_count + delta, ccs2));
    add_to_count(pp, delta);
  }
}


struct node *tree_add(struct node *node)
  //@ requires tree(?id) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id) &*& [_]tree_membership_fact(id, result);
{
  //@ open tree(id);
  //@ assert ghost_list(id, ?nodes) &*& foreach(nodes, node(id));
  //@ ghost_list_member_handle_lemma(id, node);
  //@ foreach_remove(node, nodes);
  //@ open node(id)(node);
  //@ assert [_]node->childrenGhostListId |-> ?childrenId;
  //@ assert node->firstChild |-> ?firstChild;
  //@ assert children(firstChild, ?children);
  //@ assert ghost_list(childrenId, children);
  //@ assert foreach2(children, ?childrenCounts, child(id, node));
  
  struct node *n = create_node(node, node->firstChild);
  node->firstChild = n;
  
  //@ ghost_list_add(id, n);
  //@ ghost_list_add(childrenId, n);
  //@ close children(n, cons(n, children));
  //@ open [_]n->childrenGhostListId |-> ?nChildrenId &*& ghost_list(nChildrenId, nil);
  //@ close child(id, node)(n, 1);
  //@ close foreach2(nil, nil, child(id, n));
  //@ sum_nil();
  //@ close node(id)(n);
  //@ list<struct node *> nodes1 = cons(n, remove(node, nodes));
  //@ foreach_cons(n, remove(node, nodes));
  //@ close tree_id(id);
  //@ foreach2_cons(n, 1, children, childrenCounts);
  //@ sum_cons(1, childrenCounts);
  
  add_to_count(node, 1);

  return n;
}


struct node *tree_get_parent(struct node *node)
  //@ requires tree(?id) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id) &*& (result == 0 ? true : [_]tree_membership_fact(id, result));
{
  //@ open tree(id);
  //@ assert ghost_list(id, ?nodes) &*& foreach(nodes, node(id));
  //@ ghost_list_member_handle_lemma(id, node);
  //@ foreach_remove(node, nodes);
  //@ open node(id)(node);
  struct node *p = node->parent;
  //@ if (p != 0) { ghost_list_member_handle_lemma(id, p); }
  //@ close node(id)(node);
  //@ foreach_unremove(node, nodes);
  //@ close tree(id);
  return p;
}


// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures junk();
{
    struct node *root = create_tree();
    struct node *left = tree_add(root);
    struct node *leftRight = tree_add(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    struct node *leftLeft = tree_add(left);
    struct node *leftRightRight = tree_add(leftRight);
    return 0;
}