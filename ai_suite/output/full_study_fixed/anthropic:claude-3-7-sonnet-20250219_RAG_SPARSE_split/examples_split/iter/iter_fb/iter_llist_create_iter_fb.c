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
// Helper lemma to convert from lseg to lseg2 and llist to llist_with_node
lemma void lseg_to_lseg2(struct node *first, struct node *last, list<int> v)
  requires lseg(first, last, v);
  ensures lseg2(first, last, last, v);
{
  open lseg(first, last, v);
  if (first != last) {
    lseg_to_lseg2(_n, last, t);
    close lseg2(first, last, last, v);
  } else {
    close lseg2(first, last, last, nil);
  }
}

lemma void llist_to_llist_with_node(struct llist *list, list<int> v)
  requires llist(list, v);
  ensures llist_with_node(list, v, list->first, v);
{
  open llist(list, v);
  lseg_to_lseg2(_f, _l, v);
  close llist_with_node(list, v, _f, v);
}
@*/

// TODO: make this function pass the verification
struct iter *llist_create_iter(struct llist *l)
    //@ requires [?frac]llist(l, ?v);
    //@ ensures [frac/2]llist(l, v) &*& iter(result, frac/2, l, v, v);
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    //@ open [frac]llist(l, v);
    //@ assert l->first |-> ?_f;
    //@ assert l->last |-> ?_l;
    //@ assert lseg(_f, _l, v);
    //@ assert node(_l, _, _);
    
    f = l->first;
    i->current = f;
    
    //@ close [frac/2]lseg(_f, _l, v);
    //@ close [frac/2]node(_l, _, _);
    //@ close [frac/2]llist(l, v);
    
    //@ lseg_to_lseg2(_f, _l, v);
    //@ close llist_with_node(l, v, f, v);
    //@ close [frac/2]llist_with_node(l, v, f, v);
    //@ close iter(i, frac/2, l, v, v);
    
    return i;
}