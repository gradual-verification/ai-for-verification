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
  struct node *pp = p->parent;
  if (p->count > INT_MAX - delta)
    abort();
  if (pp == 0) {
    p->count += delta;

  } else {
    
    p->count += delta;
    
    add_to_count(pp, delta);
  }
}


struct node *tree_add(struct node *node)
  //@ requires tree(?id) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id) &*& [_]tree_membership_fact(id, result);
{
  
  struct node *n = create_node(node, node->firstChild);
  node->firstChild = n;
  
  add_to_count(node, 1);

  return n;
}


struct node *tree_get_parent(struct node *node)
  //@ requires tree(?id) &*& [_]tree_membership_fact(id, node);
  //@ ensures tree(id) &*& (result == 0 ? true : [_]tree_membership_fact(id, result));
{
  struct node *p = node->parent;
  return p;
}


int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    //@ int id = create_ghost_list<struct node *>();
    //@ close tree_id(id);
    //@ close ghost_list(id, nil);
    //@ close foreach(nil, node(id));
    //@ close tree(id);
    
    struct node *root = create_tree();
    //@ open tree(id);
    //@ assert ghost_list(id, ?nodes);
    //@ assert foreach(nodes, node(id));
    //@ ghost_list_member_handle_lemma(id, root);
    //@ close tree(id);
    
    struct node *left = tree_add(root);
    //@ open tree(id);
    //@ assert ghost_list(id, ?nodes1);
    //@ assert foreach(nodes1, node(id));
    //@ ghost_list_member_handle_lemma(id, left);
    //@ close tree(id);
    
    struct node *leftRight = tree_add(left);
    //@ open tree(id);
    //@ assert ghost_list(id, ?nodes2);
    //@ assert foreach(nodes2, node(id));
    //@ ghost_list_member_handle_lemma(id, leftRight);
    //@ close tree(id);
    
    struct node *leftRightParent = tree_get_parent(leftRight);
    //@ open tree(id);
    //@ assert ghost_list(id, ?nodes3);
    //@ assert foreach(nodes3, node(id));
    //@ ghost_list_member_handle_lemma(id, leftRightParent);
    //@ close tree(id);
    
    struct node *leftLeft = tree_add(left);
    //@ open tree(id);
    //@ assert ghost_list(id, ?nodes4);
    //@ assert foreach(nodes4, node(id));
    //@ ghost_list_member_handle_lemma(id, leftLeft);
    //@ close tree(id);
    
    struct node *leftRightRight = tree_add(leftRight);
    //@ open tree(id);
    //@ assert ghost_list(id, ?nodes5);
    //@ assert foreach(nodes5, node(id));
    //@ ghost_list_member_handle_lemma(id, leftRightRight);
    //@ close tree(id);
    
    return 0;
}