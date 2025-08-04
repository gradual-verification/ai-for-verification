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
lemma void lseg_append_node(struct node* n1, struct node* n2)
  requires lseg(n1, n2, ?v) &*& node(n2, ?n3, ?x);
  ensures lseg(n1, n3, append(v, cons(x, nil)));
{
  open lseg(n1, n2, v);
  if (n1 == n2) {
    close lseg(n3, n3, nil);
    close lseg(n2, n3, cons(x, nil));
  } else {
    lseg_append_node(n1->next, n2);
    close lseg(n1, n3, append(v, cons(x, nil)));
  }
}
@*/

// TODO: make this function pass the verification
void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  //@ open llist(list, _v);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  //@ close node(l, n, x);
  list->last = n;
  //@ lseg_append_node(list->first, l);
  //@ close llist(list, append(_v, cons(x, nil)));
}