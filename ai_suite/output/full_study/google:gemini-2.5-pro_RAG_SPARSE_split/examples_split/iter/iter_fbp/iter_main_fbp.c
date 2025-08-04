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

predicate lseg2(struct node *first, struct node *last, struct node *final, list<int> v;) =
  switch (v) {
    case nil: return first == last;
    case cons(head, tail):
      return first != final &*& node(first, ?next, head) &*& lseg2(next, last, final, tail);
  };
@*/


struct iter {
    struct node *current;
};

/*@

predicate llist_with_node(struct llist *list, list<int> v0, struct node *n, list<int> vn) =
  list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, _, _) &*& v0 == append(v1, vn);

predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

lemma void lseg_append(struct node *n1, struct node *n2)
    requires lseg(n1, n2, ?v) &*& node(n2, ?next, ?val);
    ensures lseg(n1, next, append(v, cons(val, nil)));
{
    open lseg(n1, n2, v);
    if (n1 == n2) {
        close lseg(n1, next, cons(val, nil));
    } else {
        lseg_append(n1->next, n2);
        close lseg(n1, next, append(v, cons(val, nil)));
    }
}

lemma void lseg2_add(struct node *first, struct node *last, struct node *final)
    requires lseg2(first, last, final, ?v) &*& last != final &*& node(last, ?next, ?val);
    ensures lseg2(first, next, final, append(v, cons(val, nil)));
{
    open lseg2(first, last, final, v);
    switch(v) {
        case nil:
            close lseg2(first, next, final, cons(val, nil));
        case cons(h, t):
            lseg2_add(first->next, last, final);
            close lseg2(first, next, final, append(v, cons(val, nil)));
    }
}

lemma void lseg2_append_lseg(struct node *first, struct node *mid, struct node *last)
    requires [?frac]lseg2(first, mid, last, ?v1) &*& [frac]lseg(mid, last, ?v2);
    ensures [frac]lseg(first, last, append(v1, v2));
{
    open [frac]lseg2(first, mid, last, v1);
    switch(v1) {
        case nil:
            break;
        case cons(h, t):
            lseg2_append_lseg(first->next, mid, last);
            close [frac]lseg(first, last, append(v1, v2));
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
  //@ open chars(n, sizeof(struct node), _);
  //@ close node(n, 0, 0);
  l->first = n;
  l->last = n;
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}


void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  //@ open llist(list, _v);
  //@ assert list->first |-> ?f &*& list->last |-> ?l_node;
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open chars(n, sizeof(struct node), _);
  //@ close node(n, 0, 0);
  l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ lseg_append(f, l);
  //@ close lseg(n, n, nil);
  //@ close llist(list, append(_v, cons(x, nil)));
}


void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  //@ open llist(list, ?v);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, ?v_rem) &*& malloc_block_llist(list) &*& node(l, _, _);
  {
    //@ open lseg(n, l, v_rem);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(l, l, _);
  //@ open node(l, _, _);
  free(l);
  free(list);
}


struct iter *llist_create_iter(struct llist *l)
    //@ requires [?frac]llist(l, ?v);
    //@ ensures [frac/2]llist(l, v) &*& iter(result, frac/2, l, v, v);
{
    struct iter *i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    //@ open [frac]llist(l, v);
    //@ assert [frac]l->first |-> ?f;
    //@ close [frac/2]llist(l, v);
    //@ close [frac/2]lseg2(f, f, l->last, nil);
    //@ close [frac/2]llist_with_node(l, v, f, v);
    
    i->current = l->first;
    //@ close iter(i, frac/2, l, v, v);
    return i;
}


int iter_next(struct iter *i)
    //@ requires iter(i, ?f, ?l, ?v0, ?v) &*& switch (v) { case nil: return false; case cons(h, t): return true; };
    //@ ensures switch (v) { case nil: return false; case cons(h, t): return result == h &*& iter(i, f, l, v0, t); };
{
    //@ open iter(i, f, l, v0, v);
    //@ open llist_with_node(l, v0, i->current, v);
    //@ assert l->first |-> ?first_node &*& l->last |-> ?last_node;
    //@ switch(v) { case nil: case cons(h,t): }
    //@ open lseg(i->current, last_node, v);
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ lseg2_add(first_node, c, last_node);
    //@ close llist_with_node(l, v0, n, tail(v));
    //@ close iter(i, f, l, v0, tail(v));
    return value;
}


void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ open [f1]llist_with_node(l, v0, i->current, v);
    //@ open [f2]llist(l, v0);
    //@ assert [f1]l->first |-> ?f &*& [f2]l->first |-> f;
    //@ assert [f1]l->last |-> ?l_node &*& [f2]l->last |-> l_node;
    //@ lseg2_append_lseg(f, i->current, l_node);
    free(i);
    //@ close [f1+f2]llist(l, v0);
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