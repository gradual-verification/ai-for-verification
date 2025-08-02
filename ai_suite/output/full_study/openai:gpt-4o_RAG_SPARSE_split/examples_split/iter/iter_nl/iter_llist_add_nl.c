#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
predicate nodes(struct node *n, struct node *last, list<int> values) =
  n == last ? 
    values == nil 
  : 
    n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, last, ?vs) &*& values == cons(v, vs);

predicate llist(struct llist *list, list<int> values) =
  list->first |-> ?first &*& list->last |-> ?last &*& malloc_block_llist(list) &*& nodes(first, last, values);
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
    //@ close nodes(l, n, _);
  } else {
    list->first = n;
  }
  list->last = n;
  //@ close nodes(n, 0, cons(x, nil));
  //@ close llist(list, append(values, cons(x, nil)));
}