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
@*/


struct iter {
    struct node *current;
};

/*@

predicate llist_with_node(struct llist *list, list<int> v0, struct node *n, list<int> vn) =
  list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, _, _) &*& v0 == append(v1, vn);

predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

@*/

/*@

lemma void lseg2_lseg_append(struct node *n)
  requires [?frac]lseg2(?f, n, ?l, ?vs1) &*& [frac]lseg(n, l, ?vs2);
  ensures [frac]lseg(f, l, append(vs1, vs2));
{
  open lseg2(f, n, l, vs1);
  switch (vs1) {
    case nil:
    case cons(h, t):
      open [frac]node(f, ?next, h);
      lseg2_lseg_append(n);
      close [frac]node(f, next, h);
      close [frac]lseg(f, l, append(vs1, vs2));
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
    //@ open [frac/2]llist(l, v);
    f = l->first;
    i->current = f;
    //@ struct node *last = l->last;
    //@ close [frac/2]lseg2(f, f, last, nil);
    //@ close [frac/2]llist_with_node(l, v, f, v);
    //@ close iter(i, frac/2, l, v, v);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?f, ?l, ?v0, ?v) &*& switch (v) { case nil: return false; case cons(h, t): return true; };
    //@ ensures switch (v) { case nil: return false; case cons(h, t): return result == h &*& iter(i, f, l, v0, t); };
{
    //@ open iter(i, f, l, v0, v);
    struct node *c = i->current;
    //@ open llist_with_node(l, v0, c, v);
    //@ open lseg(c, ?last, v);
    //@ open node(c, _, _);
    int value = c->value;
    struct node *n = c->next;
    //@ close [f]node(c, n, value);
    //@ assert [f]lseg2(?first, _, _, ?vleft);
    //@ lseg2_add(first);
    i->current = n;
    //@ assert [f]lseg(n, last, ?tail);
    //@ append_assoc(vleft, cons(value, nil), tail);
    //@ close [f]llist_with_node(l, v0, n, tail);
    //@ close iter(i, f, l, v0, tail);
    return value;
}

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ open llist_with_node(l, v0, ?n, v);
    //@ lseg2_lseg_append(n);
    free(i);
}

int main()
    //@ requires true;
    //@ ensures true;
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
