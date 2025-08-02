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
predicate nodes(struct node *n, struct node *last, list<int> values) =
  n == last ? 
    values == nil 
  : 
    n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n) &*& 
    nodes(next, last, ?values0) &*& values == cons(value, values0);

predicate llist(struct llist *list, list<int> values) =
  list->first |-> ?first &*& list->last |-> ?last &*& malloc_block_llist(list) &*&
  nodes(first, last, values) &*& last != 0 ? last->next |-> 0 : true;
@*/

/*@
lemma void nodes_append(struct node *n, struct node *last, int x)
  requires nodes(n, last, ?values) &*& last->next |-> 0 &*& last->value |-> _;
  ensures nodes(n, last, values) &*& nodes(last, 0, cons(x, nil));
{
  open nodes(n, last, values);
  if (n != last) {
    nodes_append(n->next, last, x);
  }
  close nodes(n, last, values);
  close nodes(last, 0, cons(x, nil));
}
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
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  n->value = x;
  n->next = 0;
  
  //@ open llist(list, values);
  l = list->last;
  if (l != 0) {
    //@ open nodes(l, 0, _);
    l->next = n;
    //@ nodes_append(list->first, l, x);
  } else {
    list->first = n;
  }
  list->last = n;
  //@ close nodes(n, 0, cons(x, nil));
  //@ close llist(list, append(values, cons(x, nil)));
}