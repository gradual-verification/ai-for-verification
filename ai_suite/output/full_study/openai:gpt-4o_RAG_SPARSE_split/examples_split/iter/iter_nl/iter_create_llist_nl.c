#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

//@ predicate nodes(struct node *n; list<int> values) =
//@   n == 0 ? values == nil : n->next |-> ?next &*& n->value |-> _ &*& malloc_block_node(n) &*& nodes(next, ?values0) &*& values == cons(_, values0);

//@ predicate llist(struct llist *l; list<int> values) =
//@   l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*& nodes(first, values) &*& (values == nil ? first == last : last->next |-> 0 &*& last->value |-> _ &*& malloc_block_node(last));

struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close nodes(n, nil);
  //@ close llist(l, nil);
  return l;
}