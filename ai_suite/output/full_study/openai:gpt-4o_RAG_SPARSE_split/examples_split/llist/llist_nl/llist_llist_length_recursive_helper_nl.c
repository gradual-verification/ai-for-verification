#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

//@ predicate lseg(struct node *from, struct node *to, int length) =
//@   from == to ? length == 0 : from->next |-> ?next &*& from->value |-> _ &*& malloc_block_node(from) &*& lseg(next, to, length - 1);

int llist_length_recursive_helper(struct node *n1, struct node *n2)
  //@ requires lseg(n1, n2, ?length);
  //@ ensures lseg(n1, n2, length) &*& result == length;
{
  int len;
  if(n1 == n2) {
    len = 0;
  } else {
    //@ open lseg(n1, n2, length);
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
    //@ close lseg(n1, n2, length);
  }
  return len;
}