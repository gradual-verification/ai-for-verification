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
// Define a predicate for a single node
predicate node(struct node *n, int value) =
  n != 0 &*& n->next |-> _ &*& n->value |-> value &*& malloc_block_node(n);

// Define a predicate for a linked list segment
predicate lseg(struct node *from, struct node *to; list<int> values) =
  from == to ?
    values == nil
  :
    from != 0 &*& 
    from->next |-> ?next &*& 
    from->value |-> ?value &*& 
    malloc_block_node(from) &*& 
    lseg(next, to, ?tail) &*& 
    values == cons(value, tail);

// Define a predicate for the entire linked list
predicate llist(struct llist *list; list<int> values) =
  list != 0 &*& 
  list->first |-> ?first &*& 
  list->last |-> ?last &*& 
  malloc_block_llist(list) &*& 
  first != 0 &*& 
  last != 0 &*& 
  lseg(first, last, values) &*& 
  last->next |-> 0 &*& 
  last->value |-> _ &*& 
  malloc_block_node(last);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
*/
void llist_add(struct llist *list, int x)
//@ requires llist(list, ?values);
//@ ensures llist(list, append(values, cons(x, nil)));
{
  //@ open llist(list, values);
  struct node *l = list->last;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ assert l->next |-> 0;
  l->next = n;
  n->value = x;  // Fixed: assign value to the new node
  n->next = 0;   // Explicitly set next to 0 (though calloc already did this)
  list->last = n;
  //@ close lseg(n, n, nil);
  //@ close llist(list, append(values, cons(x, nil)));
}