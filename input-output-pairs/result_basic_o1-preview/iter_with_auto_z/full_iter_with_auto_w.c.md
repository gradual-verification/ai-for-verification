```c
#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

/*@
predicate node(struct node *node; struct node *next, int value) =
  node->next |-> next &*& node->value |-> value;
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? emp &*& v == nil : node(n1, ?next, ?value) &*& lseg(next, n2, ?tail) &*& v == cons(value, tail);
@*/

/*@
predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?f &*& list->last |-> ?l &*& lseg(f, l, v) &*& node(l, _, _);
@*/

struct llist {
  struct node *first;
  struct node *last;
};

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
  //@ close node(n, 0, 0); // dummy node
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list, ?v);
//@ ensures llist(list, append(v, cons(x, nil)));
{
  struct node *l;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  //@ open llist(list, v);
  //@ open node(l, ?lnext, ?lvalue); // l is the dummy node at the end
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ close node(n, 0, 0); // new dummy node
  //@ close lseg(l, n, cons(x, nil));
  //@ close lseg(list->first, n, append(v, cons(x, nil)));
  //@ close llist(list, append(v, cons(x, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?v1) &*& llist(list2, ?v2);
//@ ensures llist(list1, append(v1, v2));
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open llist(list1, v1);
  //@ open llist(list2, v2);
  //@ open node(l1, _, _);
  //@ open node(l2, _, _);
  if (f2 == l2) {
    //@ open lseg(f2, l2, ?v2_seg);
    //@ assert v2_seg == nil;
    free(l2);
    free(list2);
    //@ close llist(list1, v1);
  } else {
    //@ open lseg(f2, l2, ?v2_seg);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ close node(l1, f2->next, f2->value);
    //@ close lseg(list1->first, l2, append(v1, v2_seg));
    //@ close llist(list1, append(v1, v2));
  }
}

void llist_dispose(struct llist *list)
//@ requires llist(list, _);
//@ ensures emp;
{
  struct node *n;
  //@ open llist(list, _);
  n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant lseg(n, l, _);
  {
    //@ open lseg(n, l, _);
    //@ open node(n, ?next, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open node(l, _, _);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
//@ requires [?frac]llist(list, ?v);
//@ ensures [frac]llist(list, v) &*& result == length(v);
{
  struct node *n;
  int c = 0;
  //@ open [frac]llist(list, v);
  struct node *f = list->first;
  struct node *l = list->last;
  n = f;
  while (n != l)
  //@ invariant [frac]lseg(f, n, take(c, v)) &*& [frac]lseg(n, l, drop(c, v)) &*& c >= 0 &*& c <= length(v);
  {
    //@ open [frac]lseg(n, l, drop(c, v));
    //@ open [frac]node(n, ?next, _);
    n = n->next;
    c = c + 1;
  }
  //@ close [frac]llist(list, v);
  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list, ?v) &*& 0 <= index &*& index < length(v);
//@ ensures llist(list, v) &*& result == nth(index, v);
{
  struct node *n;
  int i = 0;
  //@ open llist(list, v);
  struct node *f = list->first;
  struct node *l = list->last;
  n = f;
  while (i < index)
  //@ invariant lseg(f, n, take(i, v)) &*& lseg(n, l, drop(i, v)) &*& i >= 0 &*& i <= index;
  {
    //@ open lseg(n, l, drop(i, v));
    //@ open node(n, ?next, _);
    n = n->next;
    i = i + 1;
  }
  //@ open lseg(n, l, drop(i, v));
  //@ open node(n, _, _);
  int value = n->value;
  //@ close node(n, n->next, value);
  //@ close lseg(n, l, drop(i, v));
  //@ close lseg(f, n, take(i, v));
  //@ close llist(list, v);
  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?v) &*& v != nil;
//@ ensures llist(l, tail(v)) &*& result == head(v);
{
  struct node *nf;
  //@ open llist(l, v);
  nf = l->first;
  //@ open lseg(nf, l->last, v);
  //@ open node(nf, ?nfn, ?nfv);
  l->first = nf->next;
  int nfv = nf->value;
  free(nf);
  //@ close lseg(l->first, l->last, tail(v));
  //@ close llist(l, tail(v));
  return nfv;
}

void main0()
//@ requires emp;
//@ ensures emp;
{
  struct llist *l = create_llist();
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);
  int x1 = llist_removeFirst(l);
  //@ assert x1 == 10;
  int x2 = llist_removeFirst(l);
  //@ assert x2 == 20;
  llist_dispose(l);
}

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
  int x = llist_removeFirst(l2);
  //@ assert x == 40;
  llist_append(l1, l2);
  int n = llist_length(l1);
  //@ assert n == 5;
  int e0 = llist_lookup(l1, 0);
  //@ assert e0 == 10;
  int e1 = llist_lookup(l1, 1);
  //@ assert e1 == 20;
  int e2 = llist_lookup(l1, 2);
  //@ assert e2 == 30;
  int e3 = llist_lookup(l1, 3);
  //@ assert e3 == 50;
  int e4 = llist_lookup(l1, 4);
  //@ assert e4 == 60;
  llist_dispose(l1);
  return 0;
}

struct iter {
  struct node *current;
};

/*@
predicate llist_with_node(struct llist *list, list<int> v0, struct node *n, list<int> vn) =
  list->first |-> ?f &*& list->last |-> ?l &*& lseg(f, n, ?v1) &*& lseg(n, l, vn) &*& v0 == append(v1, vn) &*& node(l, _, _);
predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v);
@*/

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
  //@ open [frac]llist(l, v);
  f = l->first;
  i->current = f;
  //@ close [frac/2]llist(l, v);
  //@ close iter(i, frac/2, l, v, v);
  return i;
}

int iter_next(struct iter *i)
//@ requires iter(i, ?f, ?l, ?v0, ?v) &*& v != nil;
//@ ensures iter(i, f, l, v0, tail(v)) &*& result == head(v);
{
  //@ open iter(i, f, l, v0, v);
  struct node *c = i->current; 
  //@ open llist_with_node(l, v0, c, v);
  //@ open lseg(c, l->last, v);
  //@ open node(c, ?next, ?value);
  int value = c->value;
  struct node *n = c->next;
  i->current = n;
  //@ close node(c, next, value);
  //@ close lseg(c, l->last, v);
  //@ close llist_with_node(l, v0, n, tail(v));
  //@ close iter(i, f, l, v0, tail(v));
  return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
//@ ensures [f1 + f2]llist(l, v0);
{
  //@ open iter(i, f1, l, v0, v);
  free(i);
  //@ close [f1 + f2]llist(l, v0);
}

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
  int i1e1 = iter_next(i1); //@ assert i1e1 == 5;
  int i2e1 = iter_next(i2); //@ assert i2e1 == 5;
  int i1e2 = iter_next(i1); //@ assert i1e2 == 10;
  int i2e2 = iter_next(i2); //@ assert i2e2 == 10;
  iter_dispose(i1);
  iter_dispose(i2);
  llist_dispose(l);
  return 0;
}
```
