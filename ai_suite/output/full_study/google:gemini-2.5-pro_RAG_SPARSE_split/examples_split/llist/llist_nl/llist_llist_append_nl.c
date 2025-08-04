#include "stdlib.h"
//@ #include "list.gh"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
// A segment of a linked list from 'first' up to (but not including) 'last'.
predicate lseg(struct node *first, struct node *last, list<int> values) =
    first == last ?
        values == nil
    :
        first != 0 &*&
        first->next |-> ?next &*&
        first->value |-> ?value &*&
        malloc_block_node(first) &*&
        lseg(next, last, ?values0) &*&
        values == cons(value, values0);

// A well-formed linked list, with a sentinel node at the end.
predicate llist_pred(struct llist *l, list<int> values) =
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    malloc_block_llist(l) &*&
    lseg(first, last, values) &*&
    last != 0 &*&
    last->next |-> _ &*&
    last->value |-> _ &*&
    malloc_block_node(last);

// Lemma to prove that two consecutive list segments can be joined into one.
lemma void lseg_append(struct node *p)
    requires lseg(p, ?q, ?vs1) &*& lseg(q, ?r, ?vs2);
    ensures lseg(p, r, append(vs1, vs2));
{
    open lseg(p, q, vs1);
    if (p != q) {
        lseg_append(p->next);
    }
    close lseg(p, r, append(vs1, vs2));
}
@*/


// TODO: make this function pass the verification
/***
 * Description:
The llist_append function appends the second list to the end of the first list,

@param list1: a single linked list to which another list is appended
@param list2: a single linked list to be appended to the end of list1

It makes sure that list2 is appended to the end of list1.
*/
void llist_append(struct llist *list1, struct llist *list2)
    /*@
    requires llist_pred(list1, ?vs1) &*& llist_pred(list2, ?vs2) &*& list1 != list2;
    ensures llist_pred(list1, append(vs1, vs2));
    @*/
{
  //@ open llist_pred(list1, vs1);
  //@ open llist_pred(list2, vs2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    //@ open lseg(f2, l2, vs2);
    //@ assert vs2 == nil;
    free(l2);
    free(list2);
    //@ append_nil(vs1);
    //@ close llist_pred(list1, append(vs1, vs2));
  } else {
    //@ open lseg(f2, l2, vs2);
    //@ assert f2->value |-> ?v2_head &*& f2->next |-> ?f2_next &*& malloc_block_node(f2);
    //@ assert lseg(f2_next, l2, ?vs2_tail);
    //@ assert vs2 == cons(v2_head, vs2_tail);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ close lseg(l1, l2, vs2);
    //@ lseg_append(list1->first);
    //@ close llist_pred(list1, append(vs1, vs2));
  }
}