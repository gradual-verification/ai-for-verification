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
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
@*/

/*@
lemma void distinct_nodes(struct node *n1, struct node *n2)
  requires node(n1, ?n1n, ?n1v) &*& node(n2, ?n2n, ?n2v);
  ensures node(n1, n1n, n1v) &*& node(n2, n2n, n2v) &*& n1 != n2;
{
  open node(n1, _, _);
  open node(n2, _, _);
  close node(n1, _, _);
  close node(n2, _, _);
}

lemma_auto void lseg_add(struct node *n2)
  requires lseg(?n1, n2, ?_v) &*& node(n2, ?n3, ?_x) &*& node(n3, ?n3next, ?n3value);
  ensures lseg(n1, n3, append(_v, cons(_x, nil))) &*& node(n3, n3next, n3value);
{
  distinct_nodes(n2, n3);
  open lseg(n1, n2, _v);
  if (n1 != n2) {
    distinct_nodes(n1, n3);
    lseg_add(n2);
  }
}
@*/

/*@
lemma_auto void lseg_append(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, ?_v1) &*& lseg(n2, n3, ?_v2) &*& node(n3, ?n3n, ?n3v);
  ensures lseg(n1, n3, append(_v1, _v2)) &*& node(n3, n3n, n3v);
{
  open lseg(n1, n2, _v1);
  switch (_v1) {
    case nil:
    case cons(x, v):
      distinct_nodes(n1, n3);
      lseg_append(n1->next, n2, n3);
  }
}
@*/

/*@

predicate lseg2(struct node *first, struct node *last, struct node *final, list<int> v;) =
  switch (v) {
    case nil: return first == last;
    case cons(head, tail):
      return first != final &*& node(first, ?next, head) &*& lseg2(next, last, final, tail);
  };

lemma_auto void lseg2_add(struct node *first)
  requires [?f]lseg2(first, ?last, ?final, ?v) &*& [f]node(last, ?next, ?value) &*& last != final;
  ensures [f]lseg2(first, next, final, append(v, cons(value, nil)));
{
  open lseg2(first, last, final, v);
  switch (v) {
    case nil:
      close [f]lseg2(next, next, final, nil);
    case cons(head, tail):
      open node(first, ?firstNext, head); // To produce witness field.
      lseg2_add(firstNext);
      close [f]node(first, firstNext, head);
  }
  close [f]lseg2(first, next, final, append(v, cons(value, nil)));
}

lemma_auto void lseg2_to_lseg(struct node *first)
  requires [?f]lseg2(first, ?last, ?final, ?v) &*& last == final;
  ensures [f]lseg(first, last, v);
{
  switch (v) {
    case nil:
      open lseg2(first, last, final, v);
    case cons(head, tail):
      open lseg2(first, last, final, v);
      open node(first, ?next, head);
      lseg2_to_lseg(next);
  }
}

@*/

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
  //@ lseg_add(l);
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
  //@ ensures llist(list1, append(_v1, _v2));
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open lseg(f2, l2, _v2);  // Causes case split.
  if (f2 == l2) {
    //@ if (f2 != l2) pointer_fractions_same_address(&f2->next, &l2->next);
    free(l2);
    free(list2);
  } else {
    //@ distinct_nodes(l1, l2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ lseg_append(list1->first, l1, l2);
    free(f2);
    free(list2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, ?vs);
    //@ decreases length(vs);
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ if (n != l) pointer_fractions_same_address(&n->next, &l->next);
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
  //@ close [frac]lseg2(f, f, l, nil);
  while (n != l)
    //@ invariant [frac]lseg2(f, n, l, ?_ls1) &*& [frac]lseg(n, l, ?_ls2) &*& _v == append(_ls1, _ls2) &*& c + length(_ls2) == length(_v);
    //@ decreases length(_ls2);
  {
    //@ open lseg(n, l, _ls2);
    //@ open node(n, _, _);
    struct node *next = n->next;
    //@ int value = n->value;
    //@ lseg2_add(f);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ assert [frac]lseg(next, l, ?ls3);
    //@ append_assoc(_ls1, cons(value, nil), ls3);
  }
  //@ if (n != l) pointer_fractions_same_address(&n->next, &l->next);
  //@ open lseg(n, l, _ls2);
  return c;
}

int llist_length_recursive_helper(struct node *n1, struct node *n2)
  //@ requires lseg(n1, n2, ?vs) &*& node(n2, _, _) &*& length(vs) <= INT_MAX;
  //@ ensures lseg(n1, n2, vs) &*& node(n2, _, _) &*& result == length(vs);
{
  int len;
  //@ open lseg(n1, n2, vs);
  if(n1 == n2) {
    //@ if (n1 != n2) pointer_fractions_same_address(&n1->next, &n2->next);
    len = 0;
  } else {
    //@ open node(n1, ?n1v, ?n1n);
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
   //@ close node(n1, n1v, n1n);
  }
  //@ close lseg(n1, n2, vs); 
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
    //@ invariant 0 <= i &*& i <= index &*& lseg(f, n, ?_ls1) &*& lseg(n, l, ?_ls2) &*& _v == append(_ls1, _ls2) &*& _ls2 == drop(i, _v) &*& i + length(_ls2) == length(_v);
    //@ decreases index - i;
  {
    //@ open lseg(n, l, _);
    //@ int value = n->value;
    struct node *next = n->next;
    //@ open lseg(next, l, ?ls3); // To produce a witness node for next.
    //@ lseg_add(n);
    //@ drop_n_plus_one(i, _v);
    n = next;
    i = i + 1;
    //@ append_assoc(_ls1, cons(value, nil), ls3);
  }
  //@ open lseg(n, l, _);
  int value = n->value;
  //@ lseg_append(f, n, l);
  //@ drop_n_plus_one(index, _v);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?v) &*& v != nil;
  //@ ensures llist(l, ?t) &*& v == cons(result, t);
{
  struct node *nf = l->first;
  //@ open lseg(nf, ?nl, v);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  return nfv;
}

void main0()
  //@ requires true;
  //@ ensures true;
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