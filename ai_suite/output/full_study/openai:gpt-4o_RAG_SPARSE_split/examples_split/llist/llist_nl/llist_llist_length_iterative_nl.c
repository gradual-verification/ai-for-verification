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
predicate lseg(struct node *from, struct node *to, list<int> values) =
  from == to ? 
    values == nil 
  : 
    from != 0 &*& from->value |-> ?v &*& from->next |-> ?n &*& malloc_block_node(from) &*& 
    lseg(n, to, ?vs) &*& values == cons(v, vs);

predicate llist(struct llist *list, list<int> values) =
  list->first |-> ?first &*& list->last |-> ?last &*& malloc_block_llist(list) &*&
  lseg(first, last, values);
@*/

/*@
lemma void lseg_to_lseg(struct node *from, struct node *to, struct node *mid)
  requires lseg(from, to, ?values) &*& mem(mid, values) == true;
  ensures lseg(from, mid, ?values1) &*& lseg(mid, to, ?values2) &*& append(values1, values2) == values;
{
  open lseg(from, to, values);
  if (from != to) {
    if (from == mid) {
      close lseg(from, mid, nil);
    } else {
      lseg_to_lseg(from->next, to, mid);
      close lseg(from, mid, _);
    }
  }
}

lemma void lseg_to_nodes(struct node *from)
  requires lseg(from, 0, ?values);
  ensures nodes(from, values);
{
  open lseg(from, 0, values);
  if (from != 0) {
    lseg_to_nodes(from->next);
    close nodes(from, values);
  }
}

lemma void nodes_to_lseg(struct node *from)
  requires nodes(from, ?values);
  ensures lseg(from, 0, values);
{
  open nodes(from, values);
  if (from != 0) {
    nodes_to_lseg(from->next);
    close lseg(from, 0, values);
  }
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
/*@
requires llist(list, ?values);
ensures llist(list, values) &*& result == length(values);
@*/
int llist_length_iterative(struct llist *list)
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open llist(list, values);
  //@ nodes_to_lseg(f);
  //@ close lseg(f, f, nil);
  while (n != l)
    //@ invariant lseg(f, n, ?vs1) &*& lseg(n, l, ?vs2) &*& append(vs1, vs2) == values &*& c == length(vs1);
  {
    //@ open lseg(n, l, vs2);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ close lseg(f, n, append(vs1, cons(head(vs2), nil)));
    //@ lseg_to_lseg(f, n, n);
  }
  //@ lseg_to_nodes(f);
  //@ close llist(list, values);
  return c;
}