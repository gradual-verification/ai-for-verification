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
// A list segment from `first` up to (but not including) `last`.
// It contains the data `values`. The `last` node is a sentinel.
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

// A linked list with a sentinel node.
predicate llist(struct llist *l, list<int> values) =
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    malloc_block_llist(l) &*&
    lseg(first, last, values) &*&
    last != 0 &*&
    last->next |-> _ &*&
    last->value |-> _ &*&
    malloc_block_node(last);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
    //@ requires true;
    //@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}