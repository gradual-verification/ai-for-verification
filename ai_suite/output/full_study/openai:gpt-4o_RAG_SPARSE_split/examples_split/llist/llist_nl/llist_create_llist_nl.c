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

predicate llist(struct llist *l) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*& nodes(first, last) &*& last->next |-> _ &*& last->value |-> _;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close nodes(n, n);
  //@ close llist(l);
  return l;
}