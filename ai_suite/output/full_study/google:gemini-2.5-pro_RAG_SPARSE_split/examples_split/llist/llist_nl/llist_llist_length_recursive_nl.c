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
predicate lseg(struct node *from, struct node *to, int len) =
    from == to ?
        len == 0
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> _ &*&
        malloc_block_node(from) &*&
        lseg(next, to, len - 1) &*&
        len > 0;

predicate llist(struct llist *l, int len) =
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    malloc_block_llist(l) &*&
    lseg(first, last, len);
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
    //@ requires lseg(n1, n2, ?len);
    //@ ensures lseg(n1, n2, len) &*& result == len;
{
  //@ open lseg(n1, n2, len);
  int len_val;
  if(n1 == n2) {
    len_val = 0;
  } else {
    len_val = llist_length_recursive_helper(n1->next, n2);
    len_val = len_val + 1;
  }
  //@ close lseg(n1, n2, len);
  return len_val;
}


// TODO: make this function pass the verification
/***
 * Description:
The llist_length_recursive function recursively calculates the length of the linked list.

@param l: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_recursive(struct llist *l)
    //@ requires llist(l, ?len);
    //@ ensures llist(l, len) &*& result == len;
{
  //@ open llist(l, len);
  int result = llist_length_recursive_helper(l->first, l->last);
  //@ close llist(l, len);
  return result;
}