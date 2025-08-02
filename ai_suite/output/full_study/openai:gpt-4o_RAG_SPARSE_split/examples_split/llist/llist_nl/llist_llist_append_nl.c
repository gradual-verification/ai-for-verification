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
predicate nodes(struct node *first, struct node *last; list<int> values) =
  first == last ?
    values == nil
  :
    first->next |-> ?next &*& first->value |-> ?value &*& malloc_block_node(first) &*&
    nodes(next, last, ?values0) &*& values == cons(value, values0);

predicate llist(struct llist *list; list<int> values) =
  list->first |-> ?first &*& list->last |-> ?last &*& malloc_block_llist(list) &*&
  nodes(first, last, values);
@*/

/*@
lemma void nodes_to_lseg(struct node *first, struct node *last)
  requires nodes(first, last, ?values);
  ensures lseg(first, last, values);
{
  open nodes(first, last, values);
  if (first != last) {
    nodes_to_lseg(first->next, last);
  }
  close lseg(first, last, values);
}

lemma void lseg_to_nodes(struct node *first, struct node *last)
  requires lseg(first, last, ?values);
  ensures nodes(first, last, values);
{
  open lseg(first, last, values);
  if (first != last) {
    lseg_to_nodes(first->next, last);
  }
  close nodes(first, last, values);
}
@*/

/*@
lemma void lseg_append(struct node *first, struct node *middle, struct node *last)
  requires lseg(first, middle, ?values1) &*& lseg(middle, last, ?values2);
  ensures lseg(first, last, append(values1, values2));
{
  open lseg(first, middle, values1);
  if (first != middle) {
    lseg_append(first->next, middle, last);
  }
  close lseg(first, last, append(values1, values2));
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
  //@ requires llist(list1, ?values1) &*& llist(list2, ?values2);
  //@ ensures llist(list1, append(values1, values2));
{
  //@ open llist(list1, values1);
  //@ open llist(list2, values2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    //@ nodes_to_lseg(f2, l2);
    //@ open lseg(f2, l2, values2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ lseg_append(list1->first, l1, l2);
    //@ lseg_to_nodes(list1->first, l2);
    free(f2);
    free(list2);
  }
  //@ close llist(list1, append(values1, values2));
}