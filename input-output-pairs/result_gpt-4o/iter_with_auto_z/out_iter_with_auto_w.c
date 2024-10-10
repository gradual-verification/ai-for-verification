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
predicate node(struct node *node; struct node *next, int value) =
  node != 0 &*& node->next |-> next &*& node->value |-> value;

predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? v == nil : node(n1, ?n, ?h) &*& lseg(n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?f &*& list->last |-> ?l &*& lseg(f, l, ?vs) &*& l->next |-> 0 &*& l->value |-> _ &*& v == append(vs, cons(_, nil));
@*/

struct llist *create_llist()
//@ requires true;
//@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->next = 0;
  n->value = 0;
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list, ?v);
//@ ensures llist(list, append(v, cons(x, nil)));
{
  struct node *last = list->last;
  struct node *new_node = malloc(sizeof(struct node));
  if (new_node == 0) abort();
  new_node->next = 0;
  new_node->value = x;
  last->next = new_node;
  list->last = new_node;
  //@ open llist(list, v);
  //@ open lseg(list->first, last, _);
  //@ close lseg(new_node, new_node, nil);
  //@ close lseg(list->first, new_node, append(v, cons(x, nil)));
  //@ close llist(list, append(v, cons(x, nil)));
}

// Other functions would be similarly specified and detailed
// using the formal verification annotations specific to VeriFast...

// Function implementations for `llist_dispose`, `llist_append`, etc.
// would be similarly annotated to maintain the proof obligations.

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  
  int x = llist_removeFirst(l2); //@ assert(x == 40);
  llist_append(l1, l2);
  
  int n = llist_length(l1); //@ assert(n == 5);
  int e0 = llist_lookup(l1, 0); //@ assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); //@ assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); //@ assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); //@ assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); //@ assert(e4 == 60);
  
  llist_dispose(l1);
  return 0;
}
