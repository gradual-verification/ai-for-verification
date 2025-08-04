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

lemma void lseg_join(struct node* n1, struct node* n2, struct node* n3)
  requires lseg(n1, n2, ?v1) &*& lseg(n2, n3, ?v2);
  ensures lseg(n1, n3, append(v1, v2));
{
  open lseg(n1, n2, v1);
  if (n1 != n2) {
    lseg_join(n1->next, n2, n3);
    close lseg(n1, n3, append(v1, v2));
  }
}

lemma void lseg_append(struct node* n1, struct node* n2)
  requires lseg(n1, n2, ?v1) &*& node(n2, ?n3, ?h);
  ensures lseg(n1, n3, append(v1, cons(h, nil)));
{
  open lseg(n1, n2, v1);
  if (n1 == n2) {
    close lseg(n3, n3, nil);
    close lseg(n1, n3, cons(h, nil));
  } else {
    lseg_append(n1->next, n2);
    close lseg(n1, n3, append(v1, cons(h, nil)));
  }
}

lemma void take_one_more<t>(int i, list<t> xs)
    requires 0 <= i && i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (i == 0) {
            } else {
                take_one_more(i - 1, t);
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
    invariant list->first |-> f &*& list->last |-> l &*& malloc_block_llist(list) &*&
              lseg(f, n, take(i, _v)) &*& lseg(n, l, drop(i, _v)) &*& node(l, _, _) &*&
              0 <= i &*& i <= index &*& index < length(_v);
    @*/
  {
    //@ open lseg(n, l, drop(i, _v));
    //@ assert node(n, ?next_node, ?h);
    struct node *next = n->next;
    //@ lseg_append(f, n);
    //@ take_one_more(i, _v);
    n = next;
    i = i + 1;
  }
  
  //@ open lseg(n, l, drop(index, _v));
  int value = n->value;
  //@ close lseg(n, l, drop(index, _v));
  
  //@ lseg_join(f, n, l);
  //@ append_take_drop_n(_v, index);
  
  //@ close llist(list, _v);
  return value;
}