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
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? emp &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
@*/

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

int llist_length_iterative(struct llist *list)
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

int llist_length_recursive_helper(struct node *n1, struct node *n2)
  //@ requires lseg(n1, n2, ?vs) &*& node(n2, _, _) &*& length(vs) <= INT_MAX;
  //@ ensures lseg(n1, n2, vs) &*& node(n2, _, _) &*& result == length(vs);
{
  int len;
  if(n1 == n2) {
    len = 0;
  } else {
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
  }
  return len;
}

int llist_length_recursive(struct llist *l)
  //@ requires llist(l, ?vs) &*& length(vs) <= INT_MAX;
  //@ ensures llist(l, vs) &*& result == length(vs);
{
  return llist_length_recursive_helper(l->first, l->last);
}

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
  assert(x1 == 10);
  int x2 = llist_removeFirst(l);
  assert(x2 == 20);
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
  int x = llist_removeFirst(l2); assert(x == 40);
  llist_append(l1, l2);
  int n1 = llist_length_iterative(l1); assert(n1 == 5);
  int n2 = llist_length_recursive(l1); assert(n2 == 5);
  int e0 = llist_lookup(l1, 0); assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}