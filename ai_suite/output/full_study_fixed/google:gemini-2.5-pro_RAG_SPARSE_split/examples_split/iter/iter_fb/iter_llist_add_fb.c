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
// Modified to include memory ownership, which is crucial for verification.
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
// This predicate now correctly propagates memory ownership via the 'node' predicate.
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ?
    v == nil
  :
    node(n1, ?next, ?h) &*& lseg(next, n2, ?t) &*& v == cons(h, t);

// Modified to include memory ownership for the list struct itself.
predicate llist(struct llist *list; list<int> v) =
  malloc_block_llist(list) &*&
  list->first |-> ?f &*&
  list->last |-> ?l &*&
  lseg(f, l, v) &*&
  node(l, _, _);
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
lemma void lseg_append(struct node* n1, struct node* n2)
  requires lseg(n1, n2, ?v) &*& node(n2, ?n3, ?val);
  ensures lseg(n1, n3, append(v, cons(val, nil)));
{
  open lseg(n1, n2, v);
  if (n1 == n2) {
    close lseg(n3, n3, nil);
    close lseg(n1, n3, cons(val, nil));
  } else {
    lseg_append(n1->next, n2);
    close lseg(n1, n3, append(v, cons(val, nil)));
  }
}
@*/

// TODO: make this function pass the verification
void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  //@ open llist(list, _v);
  //@ assert list->first |-> ?f &*& list->last |-> ?l_old;
  //@ assert lseg(f, l_old, _v) &*& node(l_old, ?l_old_next, ?l_old_val);

  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open node_next(n, ?n_next);
  //@ open node_value(n, ?n_val);
  //@ assert n_next == 0 &*& n_val == 0;

  l = list->last;
  //@ open node(l, l_old_next, l_old_val);

  l->next = n;
  l->value = x;

  //@ close node(l, n, x);

  list->last = n;

  //@ lseg_append(f, l);

  //@ close node(n, 0, 0);
  //@ close llist(list, append(_v, cons(x, nil)));
}