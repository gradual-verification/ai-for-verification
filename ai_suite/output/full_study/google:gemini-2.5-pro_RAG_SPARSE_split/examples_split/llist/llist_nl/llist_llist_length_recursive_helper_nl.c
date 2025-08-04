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
// A predicate representing a list segment from `from` to `to`.
// `vs` is a ghost parameter representing the sequence of integer values in the segment.
predicate lseg(struct node* from, struct node* to, list<int> vs) =
    // If `from` and `to` are the same, the segment is empty, and the list of values is nil.
    from == to ?
        vs == nil
    :
        // Otherwise, the segment is non-empty.
        from != 0 &*&
        // It consists of the current node `from`...
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        // ...followed by the rest of the segment from `next` to `to`.
        lseg(next, to, ?tail) &*&
        // The list of values is the current value `v` prepended to the tail's values.
        vs == cons(v, tail);
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
    //@ requires lseg(n1, n2, ?values);
    //@ ensures lseg(n1, n2, values) &*& result == length(values);
{
  int len;
  if(n1 == n2) {
    //@ open lseg(n1, n2, values);
    len = 0;
    //@ close lseg(n1, n2, values);
  } else {
    //@ open lseg(n1, n2, values);
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
    //@ close lseg(n1, n2, values);
  }
  return len;
}