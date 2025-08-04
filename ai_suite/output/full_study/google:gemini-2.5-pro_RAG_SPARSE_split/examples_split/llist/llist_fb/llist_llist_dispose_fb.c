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
// This predicate describes the memory layout of a single node's fields.
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value;
@*/

/*@
// This predicate describes a segment of a linked list, from `n1` up to (but not including) `n2`.
// It owns the memory for each node in this segment.
// `v` is the list of values of the nodes in this segment.
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ?
    v == nil
  :
    node(n1, ?_n, ?h) &*& malloc_block_node(n1) &*&
    lseg(_n, n2, ?t) &*& v == cons(h, t);

// This predicate describes a non-empty linked list structure with first and last pointers.
// It owns the memory for the list struct itself, and for all nodes in the list.
// The logical list of values `v` corresponds to the nodes from `first` up to (but not including) `last`.
// The value of the `last` node itself is not included in `v`.
predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*&
  lseg(_f, _l, v) &*&
  node(_l, _, _) &*& malloc_block_node(_l);
@*/


// TODO: make this function pass the verification
void llist_dispose(struct llist *list)
  //@ requires llist(list, ?v);
  //@ ensures true;
{
  //@ open llist(list, v);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, ?v_rem) &*& node(l, _, _) &*& malloc_block_node(l) &*& malloc_block_llist(list);
    //@ decreases length(v_rem);
  {
    //@ open lseg(n, l, v_rem);
    struct node *next = n->next;
    //@ open node(n, next, _);
    free(n);
    n = next;
  }
  
  // After the loop, n == l. The invariant holds with v_rem == nil.
  // We are left with: node(l, _, _) &*& malloc_block_node(l) &*& malloc_block_llist(list).
  
  //@ open node(l, _, _);
  free(l);
  free(list);
}