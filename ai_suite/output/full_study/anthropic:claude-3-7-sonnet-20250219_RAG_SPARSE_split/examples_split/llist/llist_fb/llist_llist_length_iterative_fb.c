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
@*/

/*@
lemma void lseg_length(struct node *n1, struct node *n2)
  requires [?frac]lseg(n1, n2, ?v);
  ensures [frac]lseg(n1, n2, v) &*& n1 == n2 ? length(v) == 0 : length(v) >= 1;
{
  open [frac]lseg(n1, n2, v);
  if (n1 != n2) {
    lseg_length(n1->next, n2);
  }
  close [frac]lseg(n1, n2, v);
}

lemma void lseg_distinct(struct node *n1, struct node *n2, struct node *n3)
  requires [?frac]lseg(n1, n2, ?v) &*& [frac]node(n2, n3, ?val) &*& n1 != n2;
  ensures [frac]lseg(n1, n2, v) &*& [frac]node(n2, n3, val);
{
  open [frac]lseg(n1, n2, v);
  if (n1->next == n2) {
    // Base case: n1 directly points to n2
  } else {
    // Recursive case: n1 points to some intermediate node
    lseg_distinct(n1->next, n2, n3);
  }
  close [frac]lseg(n1, n2, v);
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
  
  /*@
  if (f == l) {
    // Empty list case (or list with only one element)
    close [frac]lseg(f, l, _v);
    close [frac]llist(list, _v);
    return c;
  }
  @*/
  
  //@ lseg_length(f, l);
  //@ assert [frac]lseg(f, l, _v);
  
  //@ close [frac]lseg(n, n, nil);
  //@ assert n == f;
  
  while (n != l)
    /*@ invariant [frac]lseg(f, n, ?vs1) &*& [frac]lseg(n, l, ?vs2) &*& 
                  [frac]node(l, ?ln, ?lv) &*& 
                  _v == append(vs1, vs2) &*& c == length(vs1) &*&
                  list->first |-> f &*& list->last |-> l; @*/
  {
    //@ open [frac]lseg(n, l, vs2);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ close [frac]lseg(n, n, nil);
    //@ assert vs2 == cons(?h, ?t);
    //@ assert [frac]lseg(n, l, t);
    //@ close [frac]lseg(f, n, append(vs1, cons(h, nil)));
    //@ append_assoc(vs1, cons(h, nil), t);
  }
  
  //@ assert n == l;
  //@ assert [frac]lseg(f, l, _v);
  //@ assert c == length(_v);
  //@ close [frac]llist(list, _v);
  
  return c;
}