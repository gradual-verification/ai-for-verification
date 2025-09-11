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
// Note: Added malloc_block_node to make the predicate sound for memory management.
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
// Note: The lseg predicate describes a segment from n1 up to (but not including) n2.
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ?
    v == nil
  :
    node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

// Note: Added malloc_block_llist. The list has a sentinel node 'last'.
// The values 'v' are in the segment from 'first' to 'last'.
predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*&
  lseg(_f, _l, v) &*& node(_l, _, _);
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


// TODO: make this function pass the verification
struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  
  // The calloc contract ensures the fields of 'n' are zero-initialized.
  // We close the 'node' predicate for this new sentinel node.
  //@ close node(n, 0, 0);
  
  l->first = n;
  l->last = n;
  
  // For an empty list, 'first' and 'last' point to the same sentinel node.
  // The list segment from 'n' to 'n' is empty, corresponding to 'nil' values.
  //@ close lseg(n, n, nil);
  
  // Now all parts of the 'llist' predicate are satisfied.
  //@ close llist(l, nil);
  return l;
}