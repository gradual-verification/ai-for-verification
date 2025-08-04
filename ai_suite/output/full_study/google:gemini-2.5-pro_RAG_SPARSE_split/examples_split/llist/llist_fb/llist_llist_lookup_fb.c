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
// For soundness, memory allocation must be tracked.
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ?
    v == nil
  :
    node(n1, ?next, ?h) &*& lseg(next, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?f &*& list->last |-> ?l &*& lseg(f, l, v) &*& node(l, _, _);
@*/

/*@
lemma void lseg_append(struct node *n1, struct node *n2)
    requires lseg(n1, n2, ?v1) &*& node(n2, ?n3, ?val) &*& lseg(n3, ?n4, ?v2);
    ensures lseg(n1, n3, append(v1, cons(val, nil))) &*& lseg(n3, n4, v2);
{
    open lseg(n1, n2, v1);
    if (n1 != n2) {
        lseg_append(n1->next, n2);
    }
    close lseg(n1, n3, append(v1, cons(val, nil)));
}

lemma void lseg_merge(struct node *n1, struct node *n2, struct node *n3)
    requires lseg(n1, n2, ?v1) &*& lseg(n2, n3, ?v2);
    ensures lseg(n1, n3, append(v1, v2));
{
    open lseg(n1, n2, v1);
    if (n1 != n2) {
        lseg_merge(n1->next, n2, n3);
    }
    close lseg(n1, n3, append(v1, v2));
}

lemma void take_plus_one<t>(list<t> xs, int i)
    requires 0 <= i && i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (i == 0) {
            } else {
                take_plus_one(t, i - 1);
            }
    }
}
@*/

// TODO: make this function pass the verification
int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  while (i < index)
    /*@
    invariant
        lseg(f, n, take(i, _v)) &*& lseg(n, l, drop(i, _v)) &*&
        0 <= i &*& i <= index &*&
        list->first |-> f &*& list->last |-> l &*& node(l, _, _);
    @*/
  {
    //@ open lseg(n, l, drop(i, _v));
    //@ drop_n_plus_one(_v, i);
    struct node *next = n->next;
    //@ take_plus_one(_v, i);
    //@ lseg_append(f, n);
    n = next;
    i = i + 1;
  }
  
  //@ open lseg(n, l, drop(index, _v));
  //@ drop_n_plus_one(_v, index);
  int value = n->value;
  //@ assert value == nth(index, _v);
  
  //@ close lseg(n, l, drop(index, _v));
  //@ lseg_merge(f, n, l);
  //@ append_take_drop_n(_v, index);
  //@ close llist(list, _v);
  return value;
}