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
int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist(list, _v);
  //@ close lseg(f, f, nil);
  while (i < index)
    //@ invariant lseg(f, n, take(i, _v)) &*& lseg(n, l, drop(i, _v)) &*& i <= index;
  {
    //@ open lseg(n, l, drop(i, _v));
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ lseg_add_lemma(f);
  }
  //@ open lseg(n, l, drop(i, _v));
  int value = n->value;
  //@ close lseg(n, l, drop(i, _v));
  //@ lseg_to_llist_lemma(f, l);
  return value;
}

/*@
lemma void lseg_add_lemma(struct node *first)
  requires lseg(first, ?last, ?count) &*& last != 0 &*& last->next |-> ?next &*& last->value |-> ?value &*& malloc_block_node(last);
  ensures lseg(first, next, append(count, cons(value, nil)));
{
  open lseg(first, last, count);
  if (first == last) {
    close lseg(next, next, nil);
  } else {
    lseg_add_lemma(first->next);
  }
  close lseg(first, next, append(count, cons(value, nil)));
}

lemma void lseg_to_llist_lemma(struct node *first, struct node *last)
  requires lseg(first, last, ?v) &*& node(last, ?next, ?value);
  ensures llist(list, append(v, cons(value, nil)));
{
  open lseg(first, last, v);
  if (first == last) {
    close llist(list, cons(value, nil));
  } else {
    lseg_to_llist_lemma(first->next, last);
    close llist(list, append(v, cons(value, nil)));
  }
}
@*/