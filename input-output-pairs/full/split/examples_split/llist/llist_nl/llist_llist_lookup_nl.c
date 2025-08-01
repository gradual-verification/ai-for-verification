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
The `llist_lookup` function looks up the value at the given index in the linked list.
Note that the index in the linked list starts at 0.

@param list - Pointer to the linked list structure.
@param index - The index of the value to be looked up, which is within the range of the linked list.
@return - The value at the given index in the linked list.

It makes sure that the list is not changed, and the return value is the value at the given index in the list.
*/
int llist_lookup(struct llist *list, int index)
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  while (i < index)
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  int value = n->value;
  return value;
}

