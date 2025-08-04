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

// A predicate representing a segment of a singly-linked list,
// from node 'from' (inclusive) to node 'to' (exclusive).
// 'values' is a ghost list of the integer values in the segment.
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?tail_values) &*&
        values == cons(v, tail_values);

// A predicate for the llist structure, which contains a segment
// from 'first' to 'last'.
predicate llist(struct llist *list, list<int> values) =
    list->first |-> ?f &*&
    list->last |-> ?l &*&
    malloc_block_llist(list) &*&
    lseg(f, l, values);

// A lemma to prove that a list segment can be extended by one node.
// It takes a segment from 'from' to 'to', and the chunks for the 'to' node,
// and produces a segment from 'from' to 'to->next'.
lemma void lseg_extend(struct node *from, struct node *to)
    requires
        [?frac]lseg(from, to, ?vals) &*&
        to != 0 &*&
        [frac]to->value |-> ?v &*&
        [frac]to->next |-> ?next &*&
        [frac]malloc_block_node(to);
    ensures
        [frac]lseg(from, next, append(vals, cons(v, nil)));
{
    open [frac]lseg(from, to, vals);
    if (from == to) {
        close [frac]lseg(next, next, nil);
    } else {
        lseg_extend(from->next, to);
    }
    close [frac]lseg(from, next, append(vals, cons(v, nil)));
}

@*/

// TODO: make this function pass the verification
/***
 * Description:
The llist_length_iterative function iteratively calculates the length of the linked list,
which is the number of nodes from first (inclusive) to last (exclusive).
For example, if first = last, then the length is 0; If first's next = last, then the length is 1.

@param list: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_iterative(struct llist *list)
    //@ requires [?f]llist(list, ?values) &*& length(values) < INT_MAX;
    //@ ensures [f]llist(list, values) &*& result == length(values);
{
    //@ open [f]llist(list, values);
    struct node *f = list->first;
    struct node *n = f;
    struct node *l = list->last;
    int c = 0;
    //@ close [f]lseg(f, f, nil);
    while (n != l)
        /*@
        invariant
            [f]list->first |-> f &*& [f]list->last |-> l &*& [f]malloc_block_llist(list) &*&
            [f]lseg(f, n, ?p1_vals) &*& [f]lseg(n, l, ?p2_vals) &*&
            append(p1_vals, p2_vals) == values &*&
            c == length(p1_vals) &*& c < INT_MAX;
        @*/
    {
        //@ open [f]lseg(n, l, p2_vals);
        struct node *next = n->next;
        //@ lseg_extend(f, n);
        n = next;
        if (c == INT_MAX) abort();
        c = c + 1;
        //@ append_assoc(p1_vals, cons(head(p2_vals), nil), tail(p2_vals));
    }
    //@ open [f]lseg(l, l, ?p2_vals_final);
    //@ assert p2_vals_final == nil;
    //@ append_nil(p1_vals);
    //@ close [f]llist(list, values);
    return c;
}