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
  malloc_block_node(n) &*&
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
    result->childrenGhostListId |-> ?childrenGhostListId &*& ghost_list<struct node *>(childrenGhostListId, nil) &*&
    result->firstChild |-> 0 &*&
    result->nextSibling |-> next &*&
    result->parent |-> p &*&
    result->count |-> 1 &*&
    malloc_block_node(result);
  @*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  //@ int id = create_ghost_list<struct node *>();
  //@ n->childrenGhostListId = id;
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
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
    (parent == 0 ?
      [1/2]p->parent |-> 0 &*& p->nextSibling |-> _ &*& [1/2]p->count |-> _
    :
      parent != p &*&
      [_]ghost_list_member_handle(id, parent) &*&
      [_]parent->childrenGhostListId |-> ?parentChildrenId &*&
      [_]ghost_list_member_handle(parentChildrenId, p)) &*&
    malloc_block_node(p);
  @*/
  //@ ensures tree(id);
{
  struct node *pp = p->parent;
  if (p->count > INT_MAX - delta)
    abort();
  
  //@ open children(firstChild, children);
  //@ open foreach2(children, childrenCounts, child(id, p));
  p->count += delta;
  //@ close node(id)(p);
  
  if (pp == 0) {
    //@ foreach_unremove(p, nodes);
    //@ close tree(id);
  } else {
    //@ foreach_remove(pp, remove(p, nodes));
    //@ open node(id)(pp);
    //@ assert [_]pp->childrenGhostListId |-> ?pp_childrenId;
    //@ assert ghost_list(pp_childrenId, ?pp_children);
    //@ ghost_list_member_handle_lemma(pp_childrenId, p);
    //@ assert foreach2(?pp_children_nodes, ?pp_children_counts, child(id, pp));
    //@ foreach2_mem(p);
    //@ open foreach2_mem_results(?cs_before, ?cs_after, ?cts_before, ?p_count, ?cts_after);
    //@ open child(id, pp)(p, p_count);
    //@ int new_p_count = 1 + sum(childrenCounts);
    //@ close child(id, pp)(p, new_p_count);
    //@ foreach2_append(cs_before, cons(p, cs_after));
    //@ sum_append(cts_before, cons(p_count, cts_after));
    //@ sum_append(cts_before, cons(new_p_count, cts_after));
    //@ close tree_id(id);
    add_to_count(pp, delta);
  }
}


// TODO: make this function pass the verification
struct node *tree_add(struct node *node)
  //@ requires tree(?id) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id) &*& [_]tree_membership_fact(id, result);
{
  //@ open tree(id);
  //@ assert ghost_list<struct node *>(id, ?nodes) &*& foreach(nodes, node(id));
  //@ open tree_membership_fact(id, node);
  //@ ghost_list_member_handle_lemma(id, node);
  //@ foreach_remove(node, nodes);
  //@ open node(id)(node);
  /*
  Have:
  ghost_list(id, nodes)
  foreach(remove(node, nodes), node(id))
  [_]ghost_list_member_handle(id, node)
  malloc_block_node(node)
  
  // from node(id)(node)
  [_]node->childrenGhostListId |-> ?childrenId &*&
  node->firstChild |-> ?old_firstChild &*&
  children(old_firstChild, ?old_children) &*&
  ghost_list(childrenId, old_children) &*&
  foreach2(old_children, ?old_childrenCounts, child(id, node)) &*&
  [1/2]node->count |-> 1 + sum(old_childrenCounts) &*&
  [1/2]node->parent |-> ?parent &*&
  ... (parent part for node)
  */
  
  struct node *n = create_node(node, node->firstChild);
  /*
  Have:
  n->childrenGhostListId |-> ?nChildrenGhostListId &*& ghost_list(nChildrenGhostListId, nil) &*&
  n->firstChild |-> 0 &*&
  n->nextSibling |-> old_firstChild &*&
  n->parent |-> node &*&
  n->count |-> 1 &*&
  malloc_block_node(n)
  */
  
  //@ ghost_list_add(id, n);
  //@ ghost_list_add(childrenId, n);
  
  node->firstChild = n;
  
  // Prepare for add_to_count(node, 1)
  
  //@ close tree_id(id);
  
  // Construct node(id)(n)
  //@ close children(0, nil);
  //@ close foreach2(nil, nil, child(id, n));
  //@ close node(id)(n);
  
  // Re-assemble foreach for add_to_count
  //@ close foreach(cons(n, remove(node, nodes)), node(id));
  
  // Re-assemble node-specific parts for add_to_count
  //@ close children(n, cons(n, old_children));
  //@ close child(id, node)(n, 1);
  //@ close foreach2(cons(n, old_children), cons(1, old_childrenCounts), child(id, node));
  
  add_to_count(node, 1);

  //@ close tree_membership_fact(id, n);
  return n;
}