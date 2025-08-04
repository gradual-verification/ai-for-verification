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
// NOTE: Added malloc_block_node, which is required for 'free'.
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
// The lseg predicate describes a segment of the list, from n1 (inclusive) to n2 (exclusive).
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ?
    v == nil
  :
    node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

// The llist predicate describes a list with a sentinel node.
// 'first' points to the first data node.
// 'last' points to the sentinel node.
// The list segment 'v' is between 'first' and 'last'.
// NOTE: Added malloc_block_llist for completeness.
predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*&
  lseg(_f, _l, v) &*& node(_l, _, _);
@*/


// TODO: make this function pass the verification
int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?v) &*& v != nil;
  //@ ensures llist(l, ?t) &*& v == cons(result, t);
{
  //@ open llist(l, v);
  struct node *nf = l->first;
  //@ open lseg(nf, l->last, v);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(v));
  return nfv;
}