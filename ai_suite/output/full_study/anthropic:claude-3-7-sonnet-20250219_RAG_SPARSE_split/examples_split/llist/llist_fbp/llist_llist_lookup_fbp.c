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
// Helper lemma to split a list segment at a specific index
lemma void lseg_split(struct node *n1, struct node *n2, int index)
  requires lseg(n1, n2, ?v) &*& 0 <= index &*& index <= length(v);
  ensures lseg(n1, ?mid, take(index, v)) &*& lseg(mid, n2, drop(index, v)) &*& mid != 0;
{
  open lseg(n1, n2, v);
  if (n1 == n2) {
    close lseg(n1, n1, nil);
    close lseg(n1, n2, nil);
  } else {
    if (index == 0) {
      close lseg(n1, n1, nil);
    } else {
      lseg_split(n1->next, n2, index - 1);
      close lseg(n1, mid, take(index, v));
    }
  }
}

// Helper lemma to join two list segments
lemma void lseg_join(struct node *n1, struct node *mid, struct node *n2)
  requires lseg(n1, mid, ?v1) &*& lseg(mid, n2, ?v2);
  ensures lseg(n1, n2, append(v1, v2));
{
  open lseg(n1, mid, v1);
  if (n1 == mid) {
    // Base case: first segment is empty
  } else {
    // Recursive case
    lseg_join(n1->next, mid, n2);
    close lseg(n1, n2, append(v1, v2));
  }
}
@*/

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *l = list->last;
  //@ assert lseg(f, l, _v);
  
  struct node *n = f;
  int i = 0;
  
  //@ lseg_split(f, l, 0);
  //@ assert lseg(f, ?mid, take(0, _v)) &*& lseg(mid, l, drop(0, _v));
  //@ assert mid == f;
  
  while (i < index)
    /*@ invariant 0 <= i &*& i <= index &*& 
                 lseg(f, n, take(i, _v)) &*& 
                 lseg(n, l, drop(i, _v)) &*& 
                 n != 0; @*/
  {
    //@ open lseg(n, l, drop(i, _v));
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ close lseg(n, l, drop(i, _v));
  }
  
  //@ open lseg(n, l, drop(i, _v));
  //@ assert node(n, ?next, ?value);
  int value = n->value;
  //@ assert value == nth(0, drop(i, _v));
  //@ assert value == nth(i, _v);
  
  //@ close node(n, next, value);
  //@ close lseg(n, l, drop(i, _v));
  //@ lseg_join(f, n, l);
  //@ close llist(list, _v);
  
  return value;
}