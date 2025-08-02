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
predicate nodes(struct node *n; list<int> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?vs) &*& values == cons(v, vs);

predicate llist(struct llist *l; list<int> values) =
    l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
    nodes(first, values) &*& (values == nil ? first == 0 &*& last == 0 : last != 0);

lemma void nodes_to_llist(struct node *n)
    requires nodes(n, ?values);
    ensures llist(?l, values);
{
    // This lemma is a placeholder to show the transformation from nodes to llist.
}

lemma void llist_to_nodes(struct llist *l)
    requires llist(l, ?values);
    ensures nodes(l->first, values);
{
    // This lemma is a placeholder to show the transformation from llist to nodes.
}
//@*/

// TODO: make this function pass the verification
/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
//@ requires llist(l, ?values) &*& values != nil;
//@ ensures llist(l, tail(values)) &*& result == head(values);
int llist_removeFirst(struct llist *l)
{
  //@ open llist(l, values);
  struct node *nf = l->first;
  //@ open nodes(nf, values);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close nodes(nfn, tail(values));
  //@ close llist(l, tail(values));
  return nfv;
}