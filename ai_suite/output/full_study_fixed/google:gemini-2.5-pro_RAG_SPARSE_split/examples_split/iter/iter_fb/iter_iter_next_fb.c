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
// An expert would add malloc_block_node to ensure nodes are distinct heap objects.
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
@*/

/*@

// An expert would add `first != 0` to prevent null pointer dereferencing.
predicate lseg2(struct node *first, struct node *last, struct node *final, list<int> v;) =
  switch (v) {
    case nil: return first == last;
    case cons(head, tail):
      return first != 0 &*& first != final &*& node(first, ?next, head) &*& lseg2(next, last, final, tail);
  };
@*/

/*@
lemma void lseg2_extend(struct node *first, struct node *last, struct node *final, list<int> v)
    //@ requires [?frac]lseg2(first, last, final, v) &*& [frac]node(last, ?next, ?h) &*& last != 0 &*& last != final;
    //@ ensures [frac]lseg2(first, next, final, append(v, cons(h, nil)));
{
    open lseg2(first, last, final, v);
    switch (v) {
        case nil:
            // In this case, first == last.
            // We have [frac]node(last, next, h), which is the same as [frac]node(first, next, h).
            // We need to close lseg2(first, next, final, cons(h, nil)).
            // This expands to: first != 0 &*& first != final &*& [frac]node(first, ?n, h) &*& [frac]lseg2(n, next, final, nil).
            // We have all the necessary components.
            close [frac]lseg2(first, next, final, append(v, cons(h, nil)));
        case cons(head, tail):
            // In this case, first != last.
            // Recursively extend the tail of the segment.
            lseg2_extend(first->next, last, final, tail);
            // Then, close the predicate for the full new segment.
            close [frac]lseg2(first, next, final, append(v, cons(h, nil)));
    }
}

lemma void append_cons_r_assoc<t>(list<t> l1, t x, list<t> l2)
    //@ requires true;
    //@ ensures append(l1, cons(x, l2)) == append(append(l1, cons(x, nil)), l2);
{
    switch(l1) {
        case nil:
        case cons(h, t):
            append_cons_r_assoc(t, x, l2);
    }
}
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
int iter_next(struct iter *i)
    //@ requires iter(i, ?f, ?l, ?v0, ?v) &*& switch (v) { case nil: return false; case cons(h, t): return true; };
    //@ ensures switch (v) { case nil: return false; case cons(h, t): return result == h &*& iter(i, f, l, v0, t); };
{
    //@ open iter(i, f, l, v0, v);
    struct node *c = i->current;
    //@ open llist_with_node(l, v0, c, v);
    //@ list<int> v1 = ?v1_;
    //@ struct node *list_first = ?f_;
    //@ struct node *list_last = ?l_;
    //@ assert lseg2(list_first, c, list_last, v1);

    // Since v is not nil, lseg(c, list_last, v) is not the base case.
    //@ open lseg(c, list_last, v);
    //@ switch(v) { case nil: /* unreachable */ case cons(h, t): }

    int value = c->value;
    struct node *n = c->next;

    // The "already-iterated" segment lseg2 is extended to include the current node 'c'.
    //@ lseg2_extend(list_first, c, list_last, v1);

    i->current = n;

    // Prove that the overall list representation 'v0' remains consistent.
    //@ append_cons_r_assoc(v1, value, tail(v));

    // Re-establish the iterator and list predicates for the new state.
    //@ close llist_with_node(l, v0, n, tail(v));
    //@ close iter(i, f, l, v0, tail(v));

    return value;
}