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
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*& lseg(_f, _l, v) &*& node(_l, _, _);
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
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v);

@*/


// TODO: make this function pass the verification
void llist_dispose(struct llist *list)
  //@ requires llist(list, ?v);
  //@ ensures true;
{
  //@ open llist(list, v);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, ?v_rem) &*& node(l, _, _) &*& list->first |-> _ &*& list->last |-> l &*& malloc_block_llist(list);
  {
    //@ open lseg(n, l, v_rem);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(l, l, _); // When n == l, the remaining segment is empty.
  free(l);
  free(list);
}