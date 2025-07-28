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


// TODO: make this function pass the verification
/***
 * Description:
The `iter_next` function returns the value of the current node of the iterator
and moves the iterator to the next node. It requires that the iterator is not at the end of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param i - Iterator of the linked list.
@return - The value of the original node that the iterator is at.
*/
int iter_next(struct iter *i)
{
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    return value;
}

