#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

// Node predicate
/*@
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

// lseg predicate
/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? emp : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
@*/

// lseg2 predicate
/*@
predicate lseg2(struct node *first, struct node *last, struct node *final, list<int> v;) =
  switch (v) {
    case nil: return first == last;
    case cons(head, tail):
      return first != final &*& node(first, ?next, head) &*& lseg2(next, last, final, tail);
  };
@*/

// llist_with_node and iter predicates
/*@
predicate llist_with_node(struct llist *list, list<int> v0, struct node *n, list<int> vn) =
  list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, _, _) &*& v0 == append(v1, vn);

predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);
@*/

// Function to create a linked list
struct llist *create_llist()
//@ requires emp;
//@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  return l;
}

// Function to add an element to the linked list
void llist_add(struct llist *list, int x)
//@ requires llist(list, ?_v);
//@ ensures llist(list, append(_v, cons(x, nil)));
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
}

// Function to append two linked lists
void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
//@ ensures llist(list1, append(_v1, _v2));
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
}

// Function to dispose of a linked list
void llist_dispose(struct llist *list)
//@ requires llist(list, _);
//@ ensures emp;
{
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  free(l);
  free(list);
}

// Function to get the length of a linked list
int llist_length(struct llist *list)
//@ requires [?frac]llist(list, ?_v);
//@ ensures [frac]llist(list, _v) &*& result == length(_v);
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  while (n != l)
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  return c;
}

// Function to lookup an element in the linked list by index
int llist_lookup(struct llist *list, int index)
//@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
//@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  while (i < index)  
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  int value = n->value;
  return value;
}

// Function to remove the first element from the linked list
int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?v) &*& v != nil;
//@ ensures llist(l, ?t) &*& v == cons(result, t);
{
  struct node *nf = l->first;
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  return nfv;
}

// Main function to test the linked list operations
int main() //@ : main
//@ requires emp;
//@ ensures emp;
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  int x = llist_removeFirst(l2); assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1); assert(n == 5);
  int e0 = llist_lookup(l1, 0); assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

// Iterator struct
struct iter {
    struct node *current;
};

// Function to create an iterator for a linked list
struct iter *llist_create_iter(struct llist *l)
//@ requires [?frac]llist(l, ?v);
//@ ensures [frac/2]llist(l, v) &*& iter(result, frac/2, l, v, v);
{
  struct iter *i = 0;
  struct node *f = 0;
  i = malloc(sizeof(struct iter));
  if (i == 0) {
    abort();
  }
  f = l->first;
  i->current = f;
  return i;
}

// Function to get the next element from the iterator
int iter_next(struct iter *i)
//@ requires iter(i, ?f, ?l, ?v0, ?v) &*& switch (v) { case nil: return false; case cons(h, t): return true; };
//@ ensures switch (v) { case nil: return false; case cons(h, t): return result == h &*& iter(i, f, l, v0, t); };
{
  struct node *c = i->current;
  int value = c->value;
  struct node *n = c->next;
  i->current = n;
  return value;
}

// Function to dispose of an iterator
void iter_dispose(struct iter *i)
//@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
//@ ensures [f1 + f2]llist(l, v0);
{
  free(i);
}

// Function to test the iterator
int main2()
//@ requires emp;
//@ ensures emp;
{
  struct llist *l = create_llist();
  llist_add(l, 5);
  llist_add(l, 10);
  llist_add(l, 15);
  struct iter *i1 = llist_create_iter(l);
  struct iter *i2 = llist_create_iter(l);
  int i1e1 = iter_next(i1); assert(i1e1 == 5);
  int i2e1 = iter_next(i2); assert(i2e1 == 5);
  int i1e2 = iter_next(i1); assert(i1e2 == 10);
  int i2e2 = iter_next(i2); assert(i2e2 == 10);
  iter_dispose(i1);
  iter_dispose(i2);
  llist_dispose(l);
  return 0;
}
