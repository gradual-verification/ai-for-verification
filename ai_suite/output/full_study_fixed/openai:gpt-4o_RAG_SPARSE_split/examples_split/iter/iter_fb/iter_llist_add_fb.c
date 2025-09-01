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

predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
@*/

/*@
lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, ?v1) &*& node(n2, n3, ?v2) &*& lseg(n3, 0, ?v3);
  ensures lseg(n1, n3, append(v1, cons(v2, nil))) &*& lseg(n3, 0, v3);
{
  open lseg(n1, n2, v1);
  if (n1 == n2) {
    close lseg(n3, n3, nil);
  } else {
    lseg_append(n1->next, n2, n3);
  }
  close lseg(n1, n3, append(v1, cons(v2, nil)));
}
@*/

// TODO: make this function pass the verification
void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  n->next = 0;
  n->value = x;
  //@ open llist(list, _v);
  l = list->last;
  l->next = n;
  //@ lseg_append(list->first, l, n);
  list->last = n;
  //@ close llist(list, append(_v, cons(x, nil)));
}