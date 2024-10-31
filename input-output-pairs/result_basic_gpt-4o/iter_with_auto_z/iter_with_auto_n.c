#include "stdlib.h"

/*@
predicate lseg(struct node *from, struct node *to, list<int> values) =
  from == to ? values == nil :
  from != 0 &*& from->next |-> ?n &*& from->value |-> ?v &*&
  malloc_block_node(from) &*&
  lseg(n, to, ?ns) &*& values == cons(v, ns);

predicate llist(struct llist *l, list<int> values) =
  l->first |-> ?f &*& l->last |-> ?last &*&
  malloc_block_llist(l) &*& lseg(f, last, values) &*&
  last->next |-> 0 &*& last->value |-> _ &*&
  malloc_block_node(last);
@*/

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/***
 * Description:
The `create_llist` function dynamically allocates memory for a linked list structure
and initializes it with an empty node (where first = last).

@return - Pointer to the newly created linked list structure.
*/
/*@
requires true;
ensures llist(result, nil);
@*/
struct llist *create_llist()
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  return l;
}
