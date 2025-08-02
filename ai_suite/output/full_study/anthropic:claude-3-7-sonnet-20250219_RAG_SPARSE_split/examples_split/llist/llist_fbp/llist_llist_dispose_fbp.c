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


// TODO: make this function pass the verification
void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  //@ open llist(list, _);
  struct node *n = list->first;
  struct node *l = list->last;
  
  //@ assert lseg(n, l, ?v);
  //@ assert node(l, ?last_next, ?last_value);
  
  while (n != l)
    //@ invariant n != 0 &*& lseg(n, l, ?remaining) &*& node(l, last_next, last_value);
    //@ decreases length(remaining);
  {
    //@ open lseg(n, l, remaining);
    //@ assert node(n, ?next, ?value);
    struct node *next = n->next;
    //@ open node(n, next, value);
    free(n);
    n = next;
  }
  
  //@ open lseg(l, l, _);
  //@ open node(l, last_next, last_value);
  free(l);
  //@ open malloc_block_llist(list);
  free(list);
}