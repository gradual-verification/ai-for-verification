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
// Define a predicate for a linked list node
predicate node(struct node *n, int v, struct node *next) =
  n->value |-> v &*& n->next |-> next &*& malloc_block_node(n);

// Define a predicate for a non-empty linked list
predicate llist(struct llist *l, list<int> values) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  first != 0 &*& // List is non-empty
  values != nil &*& // Values list is non-empty
  lseg(first, last, values);

// Define a predicate for a linked list segment
predicate lseg(struct node *first, struct node *last, list<int> values) =
  first == last ?
    values == cons(?v, nil) &*& node(first, v, 0)
  :
    values != nil &*& node(first, head(values), ?next) &*& next != 0 &*& lseg(next, last, tail(values));
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?values);
//@ ensures llist(l, tail(values)) || (tail(values) == nil &*& l->first |-> 0 &*& l->last |-> 0 &*& malloc_block_llist(l)) &*& result == head(values);
{
  //@ open llist(l, values);
  struct node *nf = l->first;
  //@ open lseg(nf, ?last, values);
  //@ open node(nf, head(values), ?nfn);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  
  //@ if (nfn == 0) {
  //@   // If the list becomes empty
  //@   l->last = 0;
  //@ } else {
  //@   // If the list still has elements
  //@   close llist(l, tail(values));
  //@ }
  
  return nfv;
}
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
// Define a predicate for a linked list node
predicate node(struct node *n; int v, struct node *next) =
  n->value |-> v &*& n->next |-> next &*& malloc_block_node(n);

// Define a predicate for a linked list segment
predicate nodes(struct node *first, struct node *last; list<int> values) =
  first == 0 ?
    values == nil &*& last == 0
  : first == last ?
    values == cons(?v, nil) &*& node(first, v, 0)
  :
    first != 0 &*& node(first, ?v, ?next) &*& next != 0 &*& 
    nodes(next, last, ?rest_values) &*& values == cons(v, rest_values);

// Define a predicate for a linked list
predicate llist(struct llist *l; list<int> values) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  nodes(first, last, values);

// Define a predicate for a non-empty linked list
predicate llist_non_empty(struct llist *l; list<int> values) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  first != 0 &*& values != nil &*& nodes(first, last, values);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
//@ requires llist_non_empty(l, ?values);
//@ ensures llist(l, tail(values)) &*& result == head(values);
{
  //@ open llist_non_empty(l, values);
  struct node *nf = l->first;
  //@ open nodes(nf, ?last, values);
  //@ open node(nf, head(values), ?nfn);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  
  //@ if (nfn == 0) {
  //@   // If the list becomes empty
  //@   l->last = 0;
  //@   close nodes(0, 0, nil);
  //@ } else if (nfn == last) {
  //@   // If only one element remains
  //@   close nodes(nfn, last, tail(values));
  //@ } else {
  //@   // If multiple elements remain
  //@   close nodes(nfn, last, tail(values));
  //@ }
  
  //@ close llist(l, tail(values));
  return nfv;
}
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
// Define a predicate for a singly linked list
predicate nodes(struct node *n; list<int> values) =
  n == 0 ?
    values == nil
  :
    n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, ?tail_values) &*& values == cons(v, tail_values);

// Define a predicate for a linked list
predicate llist(struct llist *l; list<int> values) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  nodes(first, values) &*&
  (first == 0 ? last == 0 : true) &*&
  (values == nil ? first == 0 && last == 0 : 
    first != 0 && (last == 0 ? false : true));
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?values) &*& values != nil;
//@ ensures llist(l, tail(values)) &*& result == head(values);
{
  //@ open llist(l, values);
  struct node *nf = l->first;
  //@ open nodes(nf, values);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  
  // If the list becomes empty after removal
  if (nfn == 0) {
    l->last = 0;
  }
  
  //@ close nodes(nfn, tail(values));
  //@ close llist(l, tail(values));
  return nfv;
}
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
// Define a predicate for a singly linked list
predicate nodes(struct node *n; list<int> values) =
  n == 0 ?
    values == nil
  :
    n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, ?tail_values) &*& values == cons(v, tail_values);

// Define a predicate for a linked list
predicate llist(struct llist *l; list<int> values) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  nodes(first, values) &*&
  (values == nil ? first == 0 && last == 0 : true);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?values) &*& values != nil;
//@ ensures llist(l, tail(values)) &*& result == head(values);
{
  //@ open llist(l, values);
  struct node *nf = l->first;
  //@ open nodes(nf, values);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  
  // If the list becomes empty after removal
  if (nfn == 0) {
    l->last = 0;
  }
  
  //@ close nodes(nfn, tail(values));
  //@ close llist(l, tail(values));
  return nfv;
}