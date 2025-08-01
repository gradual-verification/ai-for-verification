#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};



// TODO: make this function pass the verification
/***
 * Description:
The llist_length_iterative function iteratively calculates the length of the linked list,
which is the number of nodes from first (inclusive) to last (exclusive).
For example, if first = last, then the length is 0; If first's next = last, then the length is 1.

@param list: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_iterative(struct llist *list)
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  while (n != l)
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  return c;
}

