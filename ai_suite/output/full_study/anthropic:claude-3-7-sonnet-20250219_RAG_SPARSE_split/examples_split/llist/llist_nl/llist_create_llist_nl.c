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
// Define a predicate for a single node
predicate node(struct node *n; int value) =
  n->next |-> ?next &*& n->value |-> value &*& malloc_block_node(n);

// Define a predicate for an empty linked list
predicate llist(struct llist *l) =
  l->first |-> ?first &*& l->last |-> first &*& 
  first != 0 &*& node(first, ?v) &*& first->next |-> 0 &*& 
  malloc_block_llist(l);
@*/

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
  //@ close node(n, 0);
  l->first = n;
  l->last = n;
  //@ close llist(l);
  return l;
}