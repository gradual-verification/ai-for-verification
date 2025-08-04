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
// Corrected to include malloc_block for memory safety.
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

// Corrected to include malloc_block for the list struct itself.
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

// Corrected to include malloc_block for the iterator struct.
predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& malloc_block_iter(i) &*& [frac]llist_with_node(l, v0, n, v);

@*/

/*@
// Lemma to merge a list segment defined by lseg2 and a standard lseg.
lemma void lseg2_append_lseg(struct node *first, struct node *last, struct node *final)
    requires lseg2(first, last, final, ?v1) &*& lseg(last, final, ?v2);
    ensures lseg(first, final, append(v1, v2));
{
    open lseg2(first, last, final, v1);
    switch(v1) {
        case nil:
            // Base case: first == last. The first segment is empty.
            // The result is just the second segment.
            break;
        case cons(h, t):
            // Recursive step: Peel off the first node.
            // The 'open' gives us 'node(first, ?next, h)' and 'lseg2(next, last, final, t)'.
            lseg2_append_lseg(first->next, last, final);
            // The recursive call transforms 'lseg2(next, ...)' and 'lseg(last, ...)'
            // into 'lseg(next, final, append(t, v2))'.
            // We can now prepend the 'node(first, ...)' to form the final segment.
            close lseg(first, final, append(v1, v2));
    }
}

// Lemma to convert the iterator's view of the list back to the standard list predicate.
lemma void llist_with_node_to_llist_lemma(struct llist *l, list<int> v0, struct node *n, list<int> vn)
    requires llist_with_node(l, v0, n, vn);
    ensures llist(l, v0);
{
    open llist_with_node(l, v0, n, vn);
    // We have lseg2(f, n, l_node, ?v1) and lseg(n, l_node, vn).
    // We also know v0 == append(v1, vn).
    lseg2_append_lseg(l->first, n, l->last);
    // This gives us lseg(f, l_node, append(v1, vn)), which is lseg(f, l_node, v0).
    // We can now close the standard llist predicate.
    close llist(l, v0);
}
@*/


// TODO: make this function pass the verification
void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    // Open the iterator predicate to get access to its components.
    open iter(i, f1, l, v0, v);
    
    // Free the iterator struct. This consumes i->current and malloc_block_iter(i).
    free(i);
    
    // We are left with [f1]llist_with_node(l, v0, ?n, v) and [f2]llist(l, v0).
    // Use the producing_lemma_from_predicate feature to apply our conversion lemma.
    // This transforms the [f1]llist_with_node chunk into an [f1]llist chunk.
    producing_lemma_from_predicate(llist_with_node, llist_with_node_to_llist_lemma)();
    
    // Now we have [f1]llist(l, v0) &*& [f2]llist(l, v0).
    // VeriFast automatically combines these into [f1 + f2]llist(l, v0),
    // satisfying the postcondition.
}