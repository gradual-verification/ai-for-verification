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

lemma void sum_update_lemma(list<int> xs, int i, int new_val)
    requires 0 <= i &*& i < length(xs);
    ensures sum(update(xs, i, new_val)) == sum(xs) - nth(i, xs) + new_val;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (i == 0) {
            } else {
                sum_update_lemma(t, i - 1, new_val);
            }
    }
}

lemma void foreach2_remove(list<struct node*> children, list<int> counts, struct node* c)
    requires foreach2(children, counts, ?p) &*& mem(c, children) == true;
    ensures
        let i = index_of(c, children) in
        foreach2(remove_nth(i, children), remove_nth(i, counts), p) &*&
        p(c, nth(i, counts));
{
    switch(children) {
        case nil:
        case cons(h, t):
            open foreach2(children, counts, p);
            if (h == c) {
            } else {
                foreach2_remove(t, tail(counts), c);
                close foreach2(remove_nth(index_of(c, children), children), remove_nth(index_of(c, children), counts), p);
            }
    }
}

lemma void foreach2_unremove(list<struct node*> children, list<int> counts, int i, struct node* c, int c_count)
    requires
        foreach2(remove_nth(i, children), remove_nth(i, counts), ?p) &*&
        p(c, c_count) &*&
        0 <= i &*& i < length(children) &*&
        nth(i, children) == c &*& nth(i, counts) == c_count;
    ensures foreach2(children, counts, p);
{
    switch(children) {
        case nil:
        case cons(h, t):
            if (i == 0) {
                open foreach2(t, tail(counts), p);
                close foreach2(children, counts, p);
            } else {
                open foreach2(remove_nth(i, children), remove_nth(i, counts), p);
                foreach2_unremove(t, tail(counts), i - 1, c, c_count);
                close foreach2(children, counts, p);
            }
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


// TODO: make this function pass the verification
void add_to_count(struct node *p, int delta)
  /*@
  requires
    tree_id(?id) &*&
    ghost_list(id, ?nodes) &*& mem(p, nodes) == true &*&
    // The node 'p' is "broken": its count is off by -delta.
    [_]p->childrenGhostListId |-> ?childrenId &*&
    p->firstChild |-> ?firstChild &*&
    children(firstChild, ?children) &*&
    ghost_list(childrenId, children) &*&
    foreach2(children, ?childrenCounts, child(id, p)) &*&
    [1/2]p->count |-> 1 + sum(childrenCounts) - delta &*&
    [1/2]p->parent |-> ?parent &*&
    delta > 0 &*&
    // If p is the root, all other nodes are fine.
    (parent == 0 ?
      [1/2]p->parent |-> 0 &*& p->nextSibling |-> _ &*& [1/2]p->count |-> (1 + sum(childrenCounts) - delta) &*&
      foreach(remove(p, nodes), node(id))
    : // If p is not the root, its parent 'parent' is also broken.
      parent != p &*&
      mem(parent, nodes) == true &*&
      foreach(remove(p, remove(parent, nodes)), node(id)) &*&
      // State of the parent 'parent'
      [_]parent->childrenGhostListId |-> ?parentChildrenId &*&
      parent->firstChild |-> ?parent_firstChild &*&
      children(parent_firstChild, ?parent_children) &*&
      ghost_list(parentChildrenId, parent_children) &*&
      let p_index_in_parent = index_of(p, parent_children) in
      foreach2(remove_nth(p_index_in_parent, parent_children), ?rem_parent_children_counts, child(id, parent)) &*&
      [1/2]p->count |-> 1 + sum(childrenCounts) &*& // Parent's view of p's count is correct before the change
      [1/2]parent->count |-> 1 + sum(rem_parent_children_counts) + (1 + sum(childrenCounts)) &*&
      [1/2]parent->parent |-> ?grandparent &*&
      (grandparent == 0 ?
          [1/2]parent->parent |-> 0 &*& parent->nextSibling |-> _ &*& [1/2]parent->count |-> _
      :
          grandparent != parent &*&
          [_]ghost_list_member_handle(id, grandparent) &*&
          [_]grandparent->childrenGhostListId |-> ?grandparentChildrenId &*&
          [_]ghost_list_member_handle(grandparentChildrenId, parent)
      )
    );
  @*/
  //@ ensures tree(id);
{
  struct node *pp = p->parent;
  if (p->count > INT_MAX - delta)
    abort();
  if (pp == 0) {
    //@ assert parent == 0;
    p->count += delta;
    //@ close node(id)(p);
    //@ foreach_unremove(p, nodes);
    //@ close tree(id);
  } else {
    //@ assert parent == pp;
    p->count += delta;
    
    // Restore node(p)
    //@ int p_new_count = 1 + sum(childrenCounts);
    //@ close child(id, pp)(p, p_new_count);
    //@ close node(id)(p);
    
    // Prepare for recursive call on pp
    //@ list<int> pp_counts_old = update(rem_parent_children_counts, p_index_in_parent, 1 + sum(childrenCounts));
    //@ list<int> pp_counts_new = update(pp_counts_old, p_index_in_parent, p_new_count);
    //@ foreach2_unremove(parent_children, pp_counts_new, p_index_in_parent, p, p_new_count);
    
    //@ sum_update_lemma(pp_counts_old, p_index_in_parent, p_new_count);
    
    //@ foreach_unremove(p, remove(pp, nodes));
    
    add_to_count(pp, delta);
  }
}