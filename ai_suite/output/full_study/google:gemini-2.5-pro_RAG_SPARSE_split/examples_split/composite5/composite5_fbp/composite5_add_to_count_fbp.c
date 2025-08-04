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

lemma void sum_update(list<int> xs, int i, int new_val)
    requires 0 <= i && i < length(xs);
    ensures sum(update(i, new_val, xs)) == sum(xs) - nth(i, xs) + new_val;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (i == 0) {
            } else {
                sum_update(t, i - 1, new_val);
            }
    }
}

lemma void foreach2_split_at<a, b>(list<a> as, list<b> bs, a x)
    requires foreach2(as, bs, ?p) &*& mem(x, as) == true;
    ensures
        exists<list<a> >(?as1) &*& exists<list<a> >(?as2) &*&
        exists<list<b> >(?bs1) &*& exists<list<b> >(?bs2) &*&
        exists<b>(?bx) &*&
        as == append(as1, cons(x, as2)) &*&
        bs == append(bs1, cons(bx, bs2)) &*&
        foreach2(as1, bs1, p) &*& p(x, bx) &*& foreach2(as2, bs2, p);
{
    open foreach2(as, bs, p);
    switch (as) {
        case nil:
        case cons(a, as0):
            switch (bs) {
                case nil:
                case cons(b, bs0):
                    if (a == x) {
                        close exists(nil); close exists(as0);
                        close exists(nil); close exists(bs0);
                        close exists(b);
                    } else {
                        foreach2_split_at(as0, bs0, x);
                        open exists(?as1_); open exists(?as2_);
                        open exists(?bs1_); open exists(?bs2_);
                        open exists(?bx_);
                        close exists(cons(a, as1_)); close exists(as2_);
                        close exists(cons(b, bs1_)); close exists(bs2_);
                        close exists(bx_);
                        close foreach2(cons(a, as1_), cons(b, bs1_), p);
                    }
            }
    }
}

lemma void foreach2_unremove<a, b>(list<a> as1, list<a> as2, list<b> bs1, list<b> bs2, a x, b bx)
    requires foreach2(as1, bs1, ?p) &*& p(x, bx) &*& foreach2(as2, bs2, p);
    ensures foreach2(append(as1, cons(x, as2)), append(bs1, cons(bx, bs2)), p);
{
    open foreach2(as1, bs1, p);
    switch (as1) {
        case nil:
            close foreach2(cons(x, as2), cons(bx, bs2), p);
        case cons(a, as1_):
            switch (bs1) {
                case nil:
                case cons(b, bs1_):
                    foreach2_unremove(as1_, as2, bs1_, bs2, x, bx);
                    close foreach2(append(as1, cons(x, as2)), append(bs1, cons(bx, bs2)), p);
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


// TODO: make this function pass the verification
void add_to_count(struct node *p, int delta)
  /*@
  requires
    p != 0 &*&
    tree_id(?id) &*&
    ghost_list(id, ?nodes) &*& mem(p, nodes) == true &*& foreach(remove(p, nodes), node(id)) &*&
    [_]p->childrenGhostListId |-> ?childrenId &*&
    p->firstChild |-> ?firstChild &*&
    children(firstChild, ?children) &*&
    ghost_list(childrenId, children) &*&
    foreach2(children, ?childrenCounts, child(id, p)) &*& delta > 0 &*&
    [1/2]p->count |-> 1 + sum(childrenCounts) - delta &*&
    [1/2]p->parent |-> ?parent &*&
    (
      parent == 0 ?
        [1/2]p->parent |-> 0 &*& p->nextSibling |-> _ &*& [1/2]p->count |-> _
      :
        parent != p &*&
        [_]ghost_list_member_handle(id, parent) &*&
        [_]parent->childrenGhostListId |-> ?parentChildrenId &*&
        [_]ghost_list_member_handle(parentChildrenId, p)
    );
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
    //@ assert pp == parent;
    //@ ghost_list_member_handle_lemma(id, pp);
    //@ foreach_unremove(p, nodes);
    //@ foreach_remove(pp, nodes);
    //@ open node(id)(pp);
    
    //@ assert pp->firstChild |-> ?pp_fc;
    //@ assert children(pp_fc, ?ppChildren);
    //@ assert [_]pp->childrenGhostListId |-> ?ppChildrenId_from_pp;
    //@ assert ppChildrenId_from_pp == parentChildrenId;
    //@ assert ghost_list(parentChildrenId, ppChildren);
    //@ assert foreach2(ppChildren, ?ppChildrenCounts, child(id, pp));
    
    //@ ghost_list_member_handle_lemma(parentChildrenId, p);
    //@ foreach2_split_at(ppChildren, ppChildrenCounts, p);
    /*@
    open exists(?as1); open exists(?as2);
    open exists(?bs1); open exists(?bs2);
    open exists(?p_count_old);
    @*/
    
    //@ open child(id, pp)(p, p_count_old);
    
    p->count += delta;
    
    //@ int p_count_new = 1 + sum(childrenCounts);
    //@ assert p_count_old == p_count_new - delta;
    
    //@ close [1/2]p->count |-> p_count_new;
    //@ close node(id)(p);
    
    //@ close [1/2]p->count |-> p_count_new;
    //@ close child(id, pp)(p, p_count_new);
    
    //@ list<int> ppChildrenCounts_new = update(index_of(p, ppChildren), p_count_new, ppChildrenCounts);
    //@ foreach2_unremove(as1, as2, bs1, bs2, p, p_count_new);
    //@ sum_update(ppChildrenCounts, index_of(p, ppChildren), p_count_new);
    //@ assert sum(ppChildrenCounts_new) == sum(ppChildrenCounts) - p_count_old + p_count_new;
    //@ assert sum(ppChildrenCounts_new) == sum(ppChildrenCounts) + delta;
    
    add_to_count(pp, delta);
  }
}