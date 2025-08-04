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
  malloc_block_node(node) &*&
  node->next |-> next &*&
  node->value |-> value;
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ?
    v == nil
  :
    node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  malloc_block_llist(list) &*&
  list->first |-> ?_f &*&
  list->last |-> ?_l &*&
  lseg(_f, _l, v) &*&
  node(_l, _, _);
@*/


// TODO: make this function pass the verification
struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}