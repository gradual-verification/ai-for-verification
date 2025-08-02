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
predicate lseg(struct node *n1, struct node *n2; list<int> values) =
  n1 == n2 ?
    values == nil
  :
    n1 != 0 &*& 
    n1->next |-> ?next &*& 
    n1->value |-> ?val &*& 
    malloc_block_node(n1) &*& 
    lseg(next, n2, ?tail_values) &*& 
    values == cons(val, tail_values);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The llist_length_recursive_helper function recursively calculates the length of the list segment between n1 and n2.
For example, if n1 = n2, then the length is 0. If n1->n->n2, then the length is calculated recursively as 2.

@param n1: the node at the beginning of the list segment
@param n2: the node at the end of the list segment

It make sures that the list segment is not changed, and the return value is the length of such list segment.
*/
int llist_length_recursive_helper(struct node *n1, struct node *n2)
//@ requires lseg(n1, n2, ?vs);
//@ ensures lseg(n1, n2, vs) &*& result == length(vs);
{
  int len;
  if(n1 == n2) {
    //@ open lseg(n1, n2, vs);
    len = 0;
    //@ close lseg(n1, n2, vs);
  } else {
    //@ open lseg(n1, n2, vs);
    //@ assert n1->next |-> ?next;
    //@ assert n1->value |-> ?val;
    //@ assert lseg(next, n2, ?tail_values);
    //@ assert vs == cons(val, tail_values);
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
    //@ close lseg(n1, n2, vs);
  }
  return len;
}