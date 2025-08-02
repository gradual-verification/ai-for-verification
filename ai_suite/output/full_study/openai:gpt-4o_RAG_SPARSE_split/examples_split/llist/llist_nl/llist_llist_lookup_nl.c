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
predicate nodes(struct node *n, struct node *last, list<int> vs) =
  n == last ? vs == nil :
  n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
  nodes(next, last, ?vs0) &*& vs == cons(v, vs0);

predicate llist(struct llist *list, list<int> vs) =
  list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*&
  nodes(f, l, vs);
@*/

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
  //@ requires llist(list, ?vs) &*& 0 <= index &*& index < length(vs);
  //@ ensures llist(list, vs) &*& result == nth(index, vs);
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open nodes(f, l, vs);
  while (i < index)
    //@ invariant nodes(n, l, drop(i, vs)) &*& 0 <= i &*& i <= index;
  {
    //@ open nodes(n, l, drop(i, vs));
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  //@ open nodes(n, l, drop(i, vs));
  int value = n->value;
  //@ close nodes(n, l, drop(i, vs));
  //@ close nodes(f, l, vs);
  return value;
}