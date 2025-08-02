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

predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*& lseg(_f, _l, v) &*& node(_l, _, _);
@*/

/*@
lemma void lseg_to_nodes(struct node *n1, struct node *n2)
  requires lseg(n1, n2, ?v);
  ensures nodes(n1, n2, v);
{
  open lseg(n1, n2, v);
  if (n1 != n2) {
    lseg_to_nodes(n1->next, n2);
  }
  close nodes(n1, n2, v);
}

lemma void nodes_to_lseg(struct node *n1, struct node *n2)
  requires nodes(n1, n2, ?v);
  ensures lseg(n1, n2, v);
{
  open nodes(n1, n2, v);
  if (n1 != n2) {
    nodes_to_lseg(n1->next, n2);
  }
  close lseg(n1, n2, v);
}
@*/

// TODO: make this function pass the verification
void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  //@ open llist(list, _);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ lseg_to_nodes(n, l);
  while (n != l)
    //@ invariant nodes(n, l, _);
  {
    //@ open nodes(n, l, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open nodes(l, l, _);
  free(l);
  free(list);
}