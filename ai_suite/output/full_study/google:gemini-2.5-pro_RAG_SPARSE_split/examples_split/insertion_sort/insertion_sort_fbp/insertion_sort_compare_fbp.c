#include "prelude.h"

struct list_node {
  int value;
  struct list_node* next;
};

/*@
  predicate list_pred(struct list_node* n;) =
    n == 0 ? 
      true
    :
      n->value |-> ?nValue &*& n->next |-> ?next &*& list_pred(next);
@*/


// TODO: make this function pass the verification
static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& result == (v0 < v1 ? -1 : v0 > v1 ? 1 : 0);
{
  if (n0->value < n1->value) {
    return -1;
  } else if (n0->value > n1->value) {
    return 1;
  } else {
    return 0;
  }
}