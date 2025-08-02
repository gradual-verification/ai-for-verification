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
predicate nodes(struct node *n, struct node *last) =
  n == last ? emp : n->next |-> ?next &*& n->value |-> _ &*& malloc_block_node(n) &*& nodes(next, last);

predicate llist(struct llist *list) =
  list->first |-> ?first &*& list->last |-> ?last &*& malloc_block_llist(list) &*& nodes(first, last) &*& malloc_block_node(last);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
  //@ requires llist(list);
  //@ ensures true;
{
  //@ open llist(list);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant nodes(n, l) &*& malloc_block_node(l);
  {
    //@ open nodes(n, l);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open nodes(l, l);
  free(l);
  free(list);
}