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
lemma void lseg_length(struct node *n1, struct node *n2)
  requires lseg(n1, n2, ?v);
  ensures lseg(n1, n2, v) &*& length(v) >= 0;
{
  open lseg(n1, n2, v);
  if (n1 != n2) {
    lseg_length(_n, n2);
  }
  close lseg(n1, n2, v);
}

lemma void lseg_add_lemma(struct node *first, struct node *last, struct node *next)
  requires lseg(first, last, ?count) &*& last != 0 &*& last->next |-> next &*& 
           last->value |-> ?value &*& malloc_block_node(last) &*& lseg(next, ?last2, ?count0);
  ensures lseg(first, next, append(count, cons(value, nil))) &*& lseg(next, last2, count0);
{
  open lseg(first, last, count);
  if (first == last) {
    close lseg(next, next, nil);
  } else {
    lseg_add_lemma(_n, last, next);
  }
  open lseg(next, last2, count0);
  close lseg(next, last2, count0);
  close lseg(first, next, append(count, cons(value, nil)));
}
@*/

int llist_length_iterative(struct llist *list)
  //@ requires [?frac]llist(list, ?_v);
  //@ ensures [frac]llist(list, _v) &*& result == length(_v);
{
  //@ open [frac]llist(list, _v);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  //@ close [frac]lseg(f, f, nil);
  
  while (n != l)
    /*@ invariant [frac]list->first |-> f &*& [frac]list->last |-> l &*& 
                  [frac]lseg(f, n, ?vs1) &*& [frac]lseg(n, l, ?vs2) &*& 
                  [frac]node(l, _, _) &*& [frac]malloc_block_llist(list) &*&
                  _v == append(vs1, vs2) &*& c == length(vs1) &*& c >= 0; @*/
  {
    //@ open [frac]lseg(n, l, vs2);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ lseg_add_lemma(f, n, l);
    //@ append_assoc(vs1, cons(head(vs2), nil), tail(vs2));
  }
  
  //@ open [frac]lseg(n, l, vs2);
  //@ assert n == l;
  //@ assert vs2 == nil;
  //@ append_nil(_v);
  //@ close [frac]llist(list, _v);
  
  return c;
}