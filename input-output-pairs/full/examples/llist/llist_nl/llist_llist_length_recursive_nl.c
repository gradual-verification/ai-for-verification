#include "stdlib.h"

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
The llist_length_recursive_helper function recursively calculates the length of the list segment between n1 and n2.
For example, if n1 = n2, then the length is 0. If n1->n->n2, then the length is calculated recursively as 2.

@param n1: the node at the beginning of the list segment
@param n2: the node at the end of the list segment

It make sures that the list segment is not changed, and the return value is the length of such list segment.
*/
int llist_length_recursive_helper(struct node *n1, struct node *n2)
{
  int len;
  if(n1 == n2) {
    len = 0;
  } else {
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
  }
  return len;
}


// TODO: make this function pass the verification
/***
 * Description:
The llist_length_recursive function recursively calculates the length of the linked list.

@param l: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_recursive(struct llist *l)
{
  return llist_length_recursive_helper(l->first, l->last);
}

