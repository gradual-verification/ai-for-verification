#include "stdlib.h"
#include <assert.h>

/*@

// A predicate for a segment of a linked list from 'first' to 'last'.
// The 'last' node is not included in the segment.
// 'values' is a ghost list representing the sequence of integer values in the segment.
predicate lseg(struct node *first, struct node *last, list<int> values) =
    first == last ?
        values == nil
    :
        first != 0 &*&
        first->next |-> ?next &*& first->value |-> ?value &*&
        malloc_block_node(first) &*&
        lseg(next, last, ?values0) &*&
        values == cons(value, values0);

// A lemma to prove that appending a node to a list segment results in a new, longer segment.
// It consumes the 'lseg' from 'first' to 'last', and the node at 'last',
// and produces a new 'lseg' from 'first' to 'next'.
lemma void lseg_append_node(struct node *first)
    requires lseg(first, ?last, ?values) &*&
             last->next |-> ?next &*& last->value |-> ?value &*&
             malloc_block_node(last);
    ensures lseg(first, next, append(values, cons(value, nil)));
{
    open lseg(first, last, values);
    if (first == last) {
        close lseg(next, next, nil);
        close lseg(first, next, append(nil, cons(value, nil)));
    } else {
        lseg_append_node(first->next);
        close lseg(first, next, append(values, cons(value, nil)));
    }
}

// A predicate representing a valid linked list structure.
// It owns the 'llist' struct and all its nodes.
// The list has a dummy node at the end, pointed to by 'last'.
predicate llist_pred(struct llist *l, list<int> values) =
    l->first |-> ?first &*& l->last |-> ?last &*&
    malloc_block_llist(l) &*&
    lseg(first, last, values) &*&
    last->next |-> _ &*& last->value |-> _ &*&
    malloc_block_node(last);

@*/

struct node {
  struct node *next;
  int value;
};

// NOTE: The original struct definition in the input file was incorrect.
// It has been corrected here to use 'struct node *' pointers.
struct llist {
  struct node *first;
  struct node *last;
};



/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
    //@ requires true;
    //@ ensures llist_pred(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close lseg(n, n, nil);
  //@ close llist_pred(l, nil);
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
    //@ requires llist_pred(list, ?vs);
    //@ ensures llist_pred(list, append(vs, cons(x, nil)));
{
  //@ open llist_pred(list, vs);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  //@ lseg_append_node(list->first);
  list->last = n;
  //@ close llist_pred(list, append(vs, cons(x, nil)));
}



/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
    //@ requires llist_pred(list, ?vs);
    //@ ensures emp;
{
  //@ open llist_pred(list, vs);
  //@ assert list->first |-> ?first &*& list->last |-> ?last;
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, _);
  {
    //@ open lseg(n, l, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(l, l, _);
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
    //@ requires llist_pred(l, ?vs) &*& vs != nil;
    //@ ensures llist_pred(l, tail(vs)) &*& result == head(vs);
{
  //@ open llist_pred(l, vs);
  struct node *nf = l->first;
  //@ open lseg(nf, l->last, vs);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist_pred(l, tail(vs));
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
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);

  //@ list<int> vs1 = cons(10, cons(20, cons(30, cons(40, nil))));
  //@ assert llist_pred(l, vs1);

  int x1 = llist_removeFirst(l);
  //@ assert llist_pred(l, tail(vs1)) &*& x1 == head(vs1);
  //@ assert x1 == 10;
  assert(x1 == 10);

  //@ list<int> vs2 = tail(vs1);
  int x2 = llist_removeFirst(l);
  //@ assert llist_pred(l, tail(vs2)) &*& x2 == head(vs2);
  //@ assert x2 == 20;
  assert(x2 == 20);

  llist_dispose(l);
}