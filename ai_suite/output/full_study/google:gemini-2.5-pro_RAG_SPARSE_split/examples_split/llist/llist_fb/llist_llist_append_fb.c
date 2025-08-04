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
  n1 == n2 ?
    v == nil
  :
    node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*&
  lseg(_f, _l, v) &*& node(_l, _, _);

lemma void lseg_append(struct node *n1, struct node *n2, list<int> v1)
    requires lseg(n1, n2, v1) &*& node(n2, ?n3, ?h) &*& lseg(n3, ?n4, ?v2);
    ensures lseg(n1, n4, append(v1, cons(h, v2)));
{
    open lseg(n1, n2, v1);
    if (n1 == n2) {
        close lseg(n1, n4, cons(h, v2));
    } else {
        lseg_append(n1->next, n2, tail(v1));
        close lseg(n1, n4, append(v1, cons(h, v2)));
    }
}
@*/


// TODO: make this function pass the verification
void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
  //@ ensures llist(list1, append(_v1, _v2));
{
  //@ open llist(list1, _v1);
  //@ open llist(list2, _v2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    //@ open lseg(f2, l2, _v2);
    //@ assert _v2 == nil;
    //@ open node(l2, _, _);
    free(l2);
    free(list2);
    //@ append_nil(_v1);
    //@ close llist(list1, append(_v1, _v2));
  } else {
    //@ open lseg(f2, l2, _v2);
    //@ assert node(f2, ?f2_next, ?f2_value) &*& lseg(f2_next, l2, ?_v2_tail) &*& _v2 == cons(f2_value, _v2_tail);
    //@ open node(l1, _, _);
    l1->next = f2->next;
    l1->value = f2->value;
    //@ close node(l1, f2_next, f2_value);
    list1->last = l2;
    //@ open node(f2, _, _);
    free(f2);
    free(list2);
    //@ lseg_append(list1->first, l1, _v1);
    //@ close llist(list1, append(_v1, _v2));
  }
}