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
// Added malloc_block_node for completeness.
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

// Added malloc_block_llist for consistency with llist_with_node.
predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*& lseg(_f, _l, v) &*& node(_l, _, _);
@*/

/*@

// The original body of lseg2 was contradictory. It has been corrected to a standard
// recursive definition, consistent with its usage as a predicate with an output parameter.
predicate lseg2(struct node *first, struct node *last, struct node *final; list<int> v) =
  first == last ?
    v == nil
  :
    first != final &*& node(first, ?next, ?head) &*& lseg2(next, last, final, ?tail) &*& v == cons(head, tail);
@*/


struct iter {
    struct node *current;
};

/*@

predicate llist_with_node(struct llist *list, list<int> v0, struct node *n, list<int> vn) =
  list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, _, _) &*& v0 == append(v1, vn);

// Added malloc_block_iter to consume the memory chunk for the iterator struct.
predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& malloc_block_iter(i) &*& [frac]llist_with_node(l, v0, n, v);

@*/


// TODO: make this function pass the verification
struct iter *llist_create_iter(struct llist *l)
    //@ requires [?frac]llist(l, ?v);
    //@ ensures [frac/2]llist(l, v) &*& iter(result, frac/2, l, v, v);
{
    //@ open [frac]llist(l, v);
    //@ assert [frac]l->first |-> ?f &*& [frac]l->last |-> ?l_last &*& [frac]malloc_block_llist(l) &*& [frac]lseg(f, l_last, v) &*& [frac]node(l_last, _, _);
    struct iter *i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ assert i->current |-> _ &*& malloc_block_iter(i);

    struct node *f_code = l->first;
    //@ assert f_code == f;
    i->current = f_code;

    // To create the iterator, we need to show that the list can be represented
    // as a segment before the current node (which is empty) and a segment
    // from the current node to the end.
    //@ close lseg2(f, f, l_last, nil);
    
    // We need to prove v == append(nil, v) for the llist_with_node predicate.
    //@ append_nil(v);
    
    // Now we can close the predicates for the postcondition, splitting the fractions.
    //@ close [frac/2]llist_with_node(l, v, f, v);
    //@ close iter(i, frac/2, l, v, v);
    //@ close [frac/2]llist(l, v);
    return i;
}