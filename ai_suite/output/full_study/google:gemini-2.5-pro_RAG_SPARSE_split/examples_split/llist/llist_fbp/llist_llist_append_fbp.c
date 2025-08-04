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

lemma void lseg_append_node(struct node* n1, struct node* n2, struct node* n3, int val)
    requires lseg(n1, n2, ?vs) &*& node(n2, n3, val);
    ensures lseg(n1, n3, append(vs, cons(val, nil)));
{
    open lseg(n1, n2, vs);
    if (n1 == n2) {
        close lseg(n1, n3, cons(val, nil));
    } else {
        lseg_append_node(n1->next, n2, n3, val);
        close lseg(n1, n3, append(vs, cons(val, nil)));
    }
}

lemma void lseg_append(struct node* n1, struct node* n2, struct node* n3)
    requires lseg(n1, n2, ?vs1) &*& lseg(n2, n3, ?vs2);
    ensures lseg(n1, n3, append(vs1, vs2));
{
    open lseg(n1, n2, vs1);
    if (n1 != n2) {
        lseg_append(n1->next, n2, n3);
        close lseg(n1, n3, append(vs1, vs2));
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
    free(l2);
    free(list2);
    //@ append_nil(_v1);
    //@ close llist(list1, append(_v1, _v2));
  } else {
    //@ open lseg(f2, l2, _v2);
    //@ assert node(f2, ?f2_next, ?h) &*& lseg(f2_next, l2, ?t) &*& _v2 == cons(h, t);
    l1->next = f2->next;
    l1->value = f2->value;
    //@ lseg_append_node(list1->first, l1, f2->next, h);
    list1->last = l2;
    free(f2);
    free(list2);
    //@ lseg_append(list1->first, f2->next, l2);
    //@ append_assoc(_v1, cons(h, nil), t);
    //@ close llist(list1, append(_v1, _v2));
  }
}