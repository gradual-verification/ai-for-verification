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
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

lemma void lseg2_lseg_merge(struct node* first, struct node* last, struct node* final)
    requires lseg2(first, last, final, ?v1) &*& lseg(last, final, ?v2);
    ensures lseg(first, final, append(v1, v2));
{
    open lseg2(first, last, final, v1);
    switch(v1) {
        case nil:
            // from lseg2: first == last
            // have: lseg(last, final, v2)
            // which is lseg(first, final, v2)
            // need: lseg(first, final, append(nil, v2))
            // which is lseg(first, final, v2). OK.
        case cons(h, t):
            // from lseg2: first != final &*& node(first, ?next, h) &*& lseg2(next, last, final, t)
            // have: lseg(last, final, v2)
            lseg2_lseg_merge(next, last, final);
            // from recursion: lseg(next, final, append(t, v2))
            // now have: node(first, next, h) &*& lseg(next, final, append(t, v2))
            // need to close: lseg(first, final, append(cons(h, t), v2))
            close lseg(first, final, append(cons(h, t), v2));
    }
}

lemma void llist_with_node_to_llist(struct llist* l)
    requires llist_with_node(l, ?v0, ?n, ?v);
    ensures llist(l, v0);
{
    open llist_with_node(l, v0, n, v);
    lseg2_lseg_merge(l->first, n, l->last);
    close llist(l, v0);
}

@*/


// TODO: make this function pass the verification
void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    open iter(i, f1, l, v0, v);
    llist_with_node_to_llist(l);
    free(i);
}