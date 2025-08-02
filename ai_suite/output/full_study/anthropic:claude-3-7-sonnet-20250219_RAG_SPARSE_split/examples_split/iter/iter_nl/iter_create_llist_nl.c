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
// Define a predicate for a linked list node
predicate node(struct node *n, int value, struct node *next) =
    n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);

// Define a predicate for a linked list
predicate llist(struct llist *l, int count) =
    l->first |-> ?first &*& 
    l->last |-> ?last &*& 
    malloc_block_llist(l) &*&
    first == last &*& // The first and last point to the same node (empty list)
    node(first, _, 0); // The node has a null next pointer
@*/

// TODO: make this function pass the verification
/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
//@ requires true;
//@ ensures llist(result, 0);
{
  struct llist *l = malloc(sizeof(struct llist));
  //@ if (l == 0) abort();
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  //@ if (n == 0) abort();
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close llist(l, 0);
  return l;
}