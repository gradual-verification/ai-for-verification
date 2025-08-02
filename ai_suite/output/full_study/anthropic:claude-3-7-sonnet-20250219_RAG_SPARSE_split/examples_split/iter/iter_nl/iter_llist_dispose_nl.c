#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
// Define a predicate for a linked list segment from 'first' to 'last'
predicate lseg(struct node *first, struct node *last; list<int> values) =
    first == last ?
        values == nil
    :
        first != 0 &*& first->next |-> ?next &*& first->value |-> ?value &*&
        malloc_block_node(first) &*& lseg(next, last, ?tail_values) &*&
        values == cons(value, tail_values);

// Define a predicate for the entire linked list
predicate llist(struct llist *list; list<int> values) =
    list->first |-> ?first &*& list->last |-> ?last &*&
    malloc_block_llist(list) &*& lseg(first, last, values) &*&
    last != 0 &*& last->next |-> _ &*& last->value |-> _ &*& malloc_block_node(last);

// Lemma to help with verification
lemma void lseg_distinct(struct node *first, struct node *last)
    requires lseg(first, last, ?values) &*& first != last;
    ensures lseg(first, last, values) &*& first != 0;
{
    open lseg(first, last, values);
    close lseg(first, last, values);
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
//@ requires llist(list, ?values);
//@ ensures true;
{
  //@ open llist(list, values);
  struct node *n = list->first;
  struct node *l = list->last;
  
  //@ lseg_distinct(n, l);
  
  while (n != l)
    //@ invariant n != 0 &*& lseg(n, l, ?remaining_values) &*& l != 0 &*& l->next |-> _ &*& l->value |-> _ &*& malloc_block_node(l);
  {
    //@ open lseg(n, l, remaining_values);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  free(l);
  free(list);
}