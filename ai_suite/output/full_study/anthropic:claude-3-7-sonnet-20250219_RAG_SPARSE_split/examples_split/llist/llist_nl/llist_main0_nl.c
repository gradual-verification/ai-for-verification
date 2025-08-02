#include "stdlib.h"

/*@
// Define an inductive type for the values in the linked list
inductive ilist = inil | icons(int, ilist);

// Define a fixpoint function to append elements to an ilist
fixpoint ilist iappend(ilist xs, ilist ys) {
    switch (xs) {
        case inil: return ys;
        case icons(h, t): return icons(h, iappend(t, ys));
    }
}
@*/

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
// Define a predicate for a linked list segment
predicate lseg(struct node *first, struct node *last, ilist values) =
    first == last ?
        values == inil
    :
        first->next |-> ?next &*& first->value |-> ?value &*&
        malloc_block_node(first) &*&
        lseg(next, last, ?values0) &*&
        values == icons(value, values0);

// Define a predicate for the linked list structure
predicate llist(struct llist *l, ilist values) =
    l->first |-> ?first &*& l->last |-> ?last &*&
    malloc_block_llist(l) &*&
    lseg(first, last, values) &*&
    last != 0 &*& last->next |-> _ &*& last->value |-> _ &*&
    malloc_block_node(last);

// Lemma to add a node to a linked list segment
lemma void lseg_add(struct node *first, struct node *last, struct node *new_last)
    requires lseg(first, last, ?values) &*& last->next |-> new_last &*& 
             last->value |-> ?value &*& malloc_block_node(last);
    ensures lseg(first, new_last, iappend(values, icons(value, inil)));
{
    open lseg(first, last, values);
    if (first == last) {
        close lseg(new_last, new_last, inil);
    } else {
        lseg_add(first->next, last, new_last);
    }
    close lseg(first, new_last, iappend(values, icons(value, inil)));
}
@*/

/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
//@ requires true;
//@ ensures result == 0 ? true : llist(result, inil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close lseg(n, n, inil);
  //@ close llist(l, inil);
  return l;
}


/***
 * Description:
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
*/
void llist_add(struct llist *list, int x)
//@ requires llist(list, ?values);
//@ ensures llist(list, iappend(values, icons(x, inil)));
{
  //@ open llist(list, values);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ lseg_add(list->first, l, n);
  //@ close llist(list, iappend(values, icons(x, inil)));
}



/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
//@ requires llist(list, ?values);
//@ ensures true;
{
  //@ open llist(list, values);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant lseg(n, l, ?remaining) &*& l != 0 &*& l->next |-> _ &*& l->value |-> _ &*& malloc_block_node(l);
  {
    //@ open lseg(n, l, remaining);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  free(l);
  free(list);
}



/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?values) &*& values != inil;
//@ ensures llist(l, ?rest) &*& values == icons(?v, rest) &*& result == v;
{
  //@ open llist(l, values);
  struct node *nf = l->first;
  //@ open lseg(nf, l->last, values);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, ?rest);
  return nfv;
}


// TODO: make this function pass the verification
/***
 * Description:
The `main0` function tests the `llist_add` and `llist_removeFirst` functions by creating a linked list,
adding elements to it, removing the first two elements, and then disposing of the list.
It asserts that the removed elements have the correct values.
*/
void main0()
//@ requires true;
//@ ensures true;
{
  struct llist *l = create_llist();
  //@ assert llist(l, inil);
  llist_add(l, 10);
  //@ assert llist(l, icons(10, inil));
  llist_add(l, 20);
  //@ assert llist(l, icons(10, icons(20, inil)));
  llist_add(l, 30);
  //@ assert llist(l, icons(10, icons(20, icons(30, inil))));
  llist_add(l, 40);
  //@ assert llist(l, icons(10, icons(20, icons(30, icons(40, inil)))));
  int x1 = llist_removeFirst(l);
  //@ assert x1 == 10;
  int x2 = llist_removeFirst(l);
  //@ assert x2 == 20;
  llist_dispose(l);
}