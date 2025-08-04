#include "stdlib.h"
//@ #include "list.gh"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
// Predicate for a segment of a linked list, also verifying the 'last' pointer.
predicate llist_nodes(struct node *n, struct node *last_node; list<int> vs) =
    n == 0 ?
        // An empty list segment.
        vs == nil &*& last_node == 0
    :
        // A non-empty list segment.
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        (
            next == 0 ?
                // This is the last node.
                n == last_node &*& vs == cons(v, nil)
            :
                // This is not the last node, recurse.
                llist_nodes(next, last_node, ?rest) &*& vs == cons(v, rest)
        );

// Predicate for the llist structure, encapsulating its invariants.
predicate llist_pred(struct llist *l; list<int> vs) =
    l->first |-> ?f &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
    llist_nodes(f, last, vs);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.
Note: This implementation is only safe for lists with more than one element. If the list has only one element,
the 'last' pointer is not updated to NULL and becomes a dangling pointer.

@param l - Pointer to the non-empty linked list structure with more than one node.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
    //@ requires llist_pred(l, ?vs) &*& length(vs) > 1;
    //@ ensures llist_pred(l, tail(vs)) &*& result == head(vs);
{
  //@ open llist_pred(l, vs);
  //@ open llist_nodes(l->first, l->last, vs);
  struct node *nf = l->first;
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist_pred(l, tail(vs));
  return nfv;
}