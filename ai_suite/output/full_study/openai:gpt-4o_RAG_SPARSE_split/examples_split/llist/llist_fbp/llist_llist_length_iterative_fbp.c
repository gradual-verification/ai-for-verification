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

// TODO: make this function pass the verification
int llist_length_iterative(struct llist *list)
  //@ requires [?frac]llist(list, ?_v);
  //@ ensures [frac]llist(list, _v) &*& result == length(_v);
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open llist(list, _v);
  //@ open lseg(f, l, _v);
  while (n != l)
  //@ invariant lseg(f, n, ?v1) &*& lseg(n, l, ?v2) &*& _v == append(v1, v2) &*& c == length(v1);
  {
    //@ open lseg(n, l, v2);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ lseg_add(f);
  }
  //@ open lseg(l, l, _);
  //@ close llist(list, _v);
  return c;
}

/*@
lemma void lseg_add(struct node *first)
  requires lseg(first, ?last, ?v1) &*& last != 0 &*& node(last, ?next, ?value) &*& lseg(next, ?end, ?v2);
  ensures lseg(first, next, append(v1, cons(value, nil))) &*& lseg(next, end, v2);
{
  open lseg(first, last, v1);
  if (first == last) {
    close lseg(next, next, nil);
  } else {
    lseg_add(first->next);
  }
  close lseg(first, next, append(v1, cons(value, nil)));
}
@*/