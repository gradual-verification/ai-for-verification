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
  node->next |-> next &*& node->value |-> value;
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
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
  list->first |-> ?f &*& list->last |-> ?l &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, _, _) &*& v0 == append(v1, vn);

predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v);

@*/

/*@
lemma void lseg2_lseg_to_lseg(struct node *f, struct node *n, struct node *l_last)
    requires [?frac]lseg2(f, n, l_last, ?v1) &*& [frac]lseg(n, l_last, ?v2);
    ensures [frac]lseg(f, l_last, append(v1, v2));
{
    open [frac]lseg2(f, n, l_last, v1);
    switch(v1) {
        case nil:
            assert f == n;
        case cons(h, t):
            lseg2_lseg_to_lseg(f->next, n, l_last);
            close [frac]lseg(f, l_last, append(v1, v2));
    }
}
@*/

// TODO: make this function pass the verification
void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    free(i);
    //@ open [f1]llist_with_node(l, v0, ?n, v);
    //@ open [f2]llist(l, v0);
    //@ lseg2_lseg_to_lseg(l->first, n, l->last);
    //@ close [f1 + f2]llist(l, v0);
}