#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
@*/

/*@

predicate lseg2(struct node *first, struct node *last, struct node *final, list<int> v;) =
  switch (v) {
    case nil: return first == last;
    case cons(head, tail):
      return first != final &*& node(first, ?next, head) &*& lseg2(next, last, final, tail);
  };
@*/


struct iter {
    struct node *current;
};

/*@

predicate llist_with_node(struct llist *list, list<int> v0, struct node *n, list<int> vn) =
  list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, _, _) &*& v0 == append(v1, vn);

predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

@*/

/*@
lemma void lseg2_extend(struct node *first, struct node *old_last, struct node *final, list<int> v_old)
    requires [?frac]lseg2(first, old_last, final, v_old) &*& [frac]node(old_last, ?new_last, ?val) &*& old_last != final;
    ensures [frac]lseg2(first, new_last, final, append(v_old, cons(val, nil)));
{
    open [frac]lseg2(first, old_last, final, v_old);
    switch(v_old) {
        case nil:
            // first == old_last
            close [frac]lseg2(new_last, new_last, final, nil);
            close [frac]lseg2(first, new_last, final, cons(val, nil));
        case cons(h, t):
            // first != final &*& [frac]node(first, ?next, h) &*& [frac]lseg2(next, old_last, final, t)
            lseg2_extend(first->next, old_last, final, t);
            close [frac]lseg2(first, new_last, final, append(v_old, cons(val, nil)));
    }
}
@*/

// TODO: make this function pass the verification
int iter_next(struct iter *i)
    //@ requires iter(i, ?f, ?l, ?v0, ?v) &*& switch (v) { case nil: return false; case cons(h, t): return true; };
    //@ ensures switch (v) { case nil: return false; case cons(h, t): return result == h &*& iter(i, f, l, v0, t); };
{
    //@ open iter(i, f, l, v0, v);
    //@ struct node *c = i->current;
    //@ open [f]llist_with_node(l, v0, c, v);
    //@ assert l->first |-> ?first_node &*& l->last |-> ?last_node;
    //@ assert [f]lseg2(first_node, c, last_node, ?v1);

    //@ switch(v) { case nil: /* unreachable */ case cons(h, t):
    //@     open [f]lseg(c, last_node, v);

    struct node *c_real = i->current;
    int value = c_real->value;
    struct node *n = c_real->next;
    i->current = n;

    //@     lseg2_extend(first_node, c, last_node, v1);
    //@     append_assoc(v1, cons(h, nil), t);
    //@     close [f]llist_with_node(l, v0, n, t);
    //@     close iter(i, f, l, v0, t);
    //@ }
    return value;
}