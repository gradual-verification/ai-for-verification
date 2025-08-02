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
// Define a predicate for a linked list segment from 'from' to 'to'
predicate lseg(struct node *from, struct node *to; int count) =
  from == to ?
    count == 0
  :
    from != 0 &*& from->next |-> ?next &*& from->value |-> ?value &*& 
    malloc_block_node(from) &*& lseg(next, to, count - 1);

// Define a predicate for the linked list structure
predicate llist(struct llist *list, int count) =
  list->first |-> ?first &*& list->last |-> ?last &*& 
  lseg(first, last, count) &*& malloc_block_llist(list);

// Lemma to add a node to a list segment
lemma void lseg_add_lemma(struct node *first)
  requires
    lseg(first, ?last, ?count) &*& last != 0 &*& last->value |-> ?value &*&
    last->next |-> ?next &*& malloc_block_node(last) &*& lseg(next, 0, ?count0);
  ensures lseg(first, next, count + 1) &*& lseg(next, 0, count0);
{
  open lseg(first, last, count);
  if(first == last) {
    close lseg(next, next, 0);
  } else {
    lseg_add_lemma(first->next);
  }
  open lseg(next, 0, count0);
  close lseg(next, 0, count0);
  close lseg(first, next, count + 1);
}

// Lemma to convert nodes to lseg
lemma void nodes_to_lseg_lemma(struct node *first)
  requires lseg(first, 0, ?count);
  ensures lseg(first, 0, count);
{
  open lseg(first, 0, count);
  if(first != 0) {
    nodes_to_lseg_lemma(first->next);
  }
  close lseg(first, 0, count);
}

// Lemma to convert lseg to nodes
lemma void lseg_to_nodes_lemma(struct node *first)
  requires lseg(first, 0, ?count);
  ensures lseg(first, 0, count);
{
  open lseg(first, 0, count);
  if(first != 0) {
    lseg_to_nodes_lemma(first->next);
  }
  close lseg(first, 0, count);
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The llist_length_iterative function iteratively calculates the length of the linked list,
which is the number of nodes from first (inclusive) to last (exclusive).
For example, if first = last, then the length is 0; If first's next = last, then the length is 1.

@param list: a single linked list

It makes sure that the list is not changed, and the return value is the length of the list.
*/
int llist_length_iterative(struct llist *list)
//@ requires llist(list, ?count);
//@ ensures llist(list, count) &*& result == count;
{
  //@ open llist(list, count);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  //@ nodes_to_lseg_lemma(f);
  //@ close lseg(f, f, 0);
  
  while (n != l)
    //@ invariant lseg(f, n, c) &*& lseg(n, l, count - c);
  {
    //@ open lseg(n, l, count - c);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ lseg_add_lemma(f);
  }
  
  //@ open lseg(n, l, count - c);
  //@ assert n == l;
  //@ assert c == count;
  //@ lseg_to_nodes_lemma(f);
  //@ close llist(list, count);
  return c;
}