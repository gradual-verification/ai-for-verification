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
  node->next |-> next &*& node->value |-> value;
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);

lemma void lseg_append_node(struct node *n1, struct node *n2)
    requires [?q]lseg(n1, n2, ?v) &*& [q]node(n2, ?n3, ?val);
    ensures [q]lseg(n1, n3, append(v, cons(val, nil)));
{
    open lseg(n1, n2, v);
    if (n1 == n2) {
        close [q]lseg(n3, n3, nil);
    } else {
        lseg_append_node(n1->next, n2);
    }
    close [q]lseg(n1, n3, append(v, cons(val, nil)));
}
@*/


// TODO: make this function pass the verification
int llist_length_iterative(struct llist *list)
  //@ requires [?frac]llist(list, ?_v);
  //@ ensures [frac]llist(list, _v) &*& result == length(_v);
{
  //@ open [frac]llist(list, _v);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  while (n != l)
    /*@ invariant [frac]list->first |-> f &*& [frac]list->last |-> l &*&
                  [frac]lseg(f, n, ?v_done) &*& [frac]lseg(n, l, ?v_rem) &*&
                  _v == append(v_done, v_rem) &*& c == length(v_done) &*&
                  [frac]node(l, _, _);
    @*/
  {
    //@ open [frac]lseg(n, l, v_rem);
    //@ assert [frac]node(n, ?next_node, ?h) &*& [frac]lseg(next_node, l, ?t) &*& v_rem == cons(h, t);
    struct node *next = n->next;
    //@ lseg_append_node(f, n);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ append_assoc(v_done, cons(h, nil), t);
  }
  
  //@ assert n == l;
  //@ open [frac]lseg(l, l, v_rem); // This shows v_rem == nil
  //@ assert _v == v_done;
  
  //@ close [frac]llist(list, _v);
  return c;
}