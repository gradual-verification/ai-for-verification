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


// TODO: make this function pass the verification
int llist_length_recursive_helper(struct node *n1, struct node *n2)
  //@ requires lseg(n1, n2, ?vs) &*& node(n2, _, _);
  //@ ensures lseg(n1, n2, vs) &*& node(n2, _, _) &*& result == length(vs);
{
  //@ open lseg(n1, n2, vs);
  int len;
  if(n1 == n2) {
    len = 0;
  } else {
    //@ open node(n1, ?next, ?h);
    len = llist_length_recursive_helper(n1->next, n2);
    //@ assert lseg(next, n2, ?t) &*& vs == cons(h, t) &*& len == length(t);
    len = len + 1;
    //@ close node(n1, next, h);
  }
  //@ close lseg(n1, n2, vs);
  return len;
}