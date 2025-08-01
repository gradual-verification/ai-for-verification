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
The llist_append function appends the second list to the end of the first list,

@param list1: a single linked list to which another list is appended
@param list2: a single linked list to be appended to the end of list1

It makes sure that list2 is appended to the end of list1.
*/
void llist_append(struct llist *list1, struct llist *list2)
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
}

