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
// Predicate to represent a list segment from n1 to n2
predicate lseg(struct node *n1, struct node *n2, int count) =
  n1 == n2 ?
    count == 0
  :
    0 < count &*& n1 != 0 &*&
    n1->value |-> ?value &*& n1->next |-> ?next &*& malloc_block_node(n1) &*&
    lseg(next, n2, count - 1);

// Predicate to represent a linked list
predicate llist(struct llist *l, int count) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  lseg(first, last, count) &*& 
  (first == 0 ? last == 0 : last != 0);
@*/

/***
 * Description:
The llist_length_recursive_helper function recursively calculates the length of the list segment between n1 and n2.
For example, if n1 = n2, then the length is 0. If n1->n->n2, then the length is calculated recursively as 2.

@param n1: the node at the beginning of the list segment
@param n2: the node at the end of the list segment

It make sures that the list segment is not changed, and the return value is the length of such list segment.
*/
int llist_length_recursive_helper(struct node *n1, struct node *n2)
//@ requires lseg(n1, n2, ?count);
//@ ensures lseg(n1, n2, count) &*& result == count;
{
  int len;
  //@ open lseg(n1, n2, count);
  if(n1 == n2) {
    len = 0;
  } else {
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
  }
  //@ close lseg(n1, n2, count);
  return len;
}

/***
 * Description:
The llist_length_recursive function recursively calculates the length of the linked list.

@param l: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_recursive(struct llist *l)
//@ requires llist(l, ?count);
//@ ensures llist(l, count) &*& result == count;
{
  //@ open llist(l, count);
  struct node *first = l->first;
  struct node *last = l->last;
  
  // Handle the case where the list is empty
  if (first == 0) {
    //@ assert last == 0;
    //@ close llist(l, 0);
    return 0;
  }
  
  // Calculate the length using the helper function
  int result = llist_length_recursive_helper(first, last);
  
  // Add 1 to include the last node (since lseg doesn't count the last node)
  result = result + 1;
  
  //@ close llist(l, count);
  return result;
}