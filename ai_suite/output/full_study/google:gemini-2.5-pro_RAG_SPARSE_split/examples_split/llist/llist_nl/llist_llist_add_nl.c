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
// A segment of a linked list from 'from' to 'to' with values 'vs'
predicate lseg(struct node* from, struct node* to; list<int> vs) =
  from == to ?
    vs == nil
  :
    from != 0 &*&
    from->next |-> ?next &*&
    from->value |-> ?v &*&
    malloc_block_node(from) &*&
    lseg(next, to, ?rest) &*&
    vs == cons(v, rest);

// A linked list with a sentinel node at the end
predicate llist(struct llist* list; list<int> vs) =
  list->first |-> ?f &*&
  list->last |-> ?l &*&
  malloc_block_llist(list) &*&
  lseg(f, l, vs) &*&
  l != 0 &*&
  l->next |-> 0 &*&
  l->value |-> _ &*&
  malloc_block_node(l);

// Lemma to extend a list segment with one more node
lemma void lseg_append_node(struct node* from, struct node* to)
  requires lseg(from, to, ?vs) &*& to != 0 &*& to->next |-> ?next &*& to->value |-> ?v &*& malloc_block_node(to);
  ensures lseg(from, next, append(vs, cons(v, nil)));
{
  open lseg(from, to, vs);
  if (from == to) {
    close lseg(next, next, nil);
    close lseg(from, next, cons(v, nil));
  } else {
    lseg_append_node(from->next, to);
    close lseg(from, next, append(vs, cons(v, nil)));
  }
}
@*/

/***
 * Description:
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
*/
void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?vs);
  //@ ensures llist(list, append(vs, cons(x, nil)));
{
  //@ open llist(list, vs);
  //@ struct node *f = list->first;
  struct node *l_old = list->last;

  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  // calloc ensures n->next |-> 0 &*& n->value |-> 0

  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;

  //@ lseg_append_node(f, l_old);
  //@ close llist(list, append(vs, cons(x, nil)));
}