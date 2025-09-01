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
  list->first |-> ?f &*& list->last |-> ?l &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, _, _) &*& v0 == append(v1, vn) &*& malloc_block_llist(list);

predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

@*/

/*@
lemma void lseg_append_node(struct node* n1, struct node* n2, list<int> v, int x, struct node* n3)
    requires lseg(n1, n2, v) &*& node(n2, n3, x);
    ensures lseg(n1, n3, append(v, cons(x, nil)));
{
    open lseg(n1, n2, v);
    if (n1 == n2) {
        close lseg(n3, n3, nil);
        close lseg(n1, n3, cons(x, nil));
    } else {
        lseg_append_node(n1->next, n2, tail(v), x, n3);
        close lseg(n1, n3, append(v, cons(x, nil)));
    }
}

lemma void lseg2_append_node(struct node* first, struct node* last, struct node* final, list<int> v, int h, struct node* next)
    requires [?frac]lseg2(first, last, final, v) &*& [frac]node(last, next, h) &*& last != final;
    ensures [frac]lseg2(first, next, final, append(v, cons(h, nil)));
{
    open [frac]lseg2(first, last, final, v);
    switch(v) {
        case nil:
            close [frac]lseg2(next, next, final, nil);
            close [frac]lseg2(first, next, final, cons(h, nil));
        case cons(head, tail):
            lseg2_append_node(first->next, last, final, tail, h, next);
            close [frac]lseg2(first, next, final, append(v, cons(h, nil)));
    }
}

lemma void lseg2_lseg_join(struct node* first, struct node* n, struct node* l_node, list<int> v1, list<int> v)
    requires [?frac]lseg2(first, n, l_node, v1) &*& [frac]lseg(n, l_node, v);
    ensures [frac]lseg(first, l_node, append(v1, v));
{
    open [frac]lseg2(first, n, l_node, v1);
    switch(v1) {
        case nil:
        case cons(h, t):
            lseg2_lseg_join(first->next, n, l_node, t, v);
            close [frac]lseg(first, l_node, append(v1, v));
    }
}

lemma void llist_with_node_to_llist(struct llist *l)
    requires [?f]llist_with_node(l, ?v0, ?n, ?v);
    ensures [f]llist(l, v0);
{
    open [f]llist_with_node(l, v0, n, v);
    assert [f]l->first |-> ?first &*& [f]l->last |-> ?last &*& [f]lseg2(first, n, last, ?v1) &*& [f]lseg(n, last, v) &*& [f]node(last, _, _) &*& v0 == append(v1, v) &*& [f]malloc_block_llist(l);
    lseg2_lseg_join(first, n, last, v1, v);
    close [f]llist(l, v0);
}

lemma void llist_to_llist_with_node_first(struct llist *l)
    requires [?f]llist(l, ?v);
    ensures [f]llist_with_node(l, v, l->first, v);
{
    open [f]llist(l, v);
    assert [f]l->first |-> ?f &*& [f]l->last |-> ?l_node &*& [f]lseg(f, l_node, v) &*& [f]node(l_node, _, _) &*& [f]malloc_block_llist(l);
    close lseg2(f, f, l_node, nil);
    close [f]llist_with_node(l, v, f, v);
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
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}


void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  //@ open llist(list, _v);
  //@ assert list->first |-> ?f &*& list->last |-> ?l_old &*& lseg(f, l_old, _v) &*& node(l_old, _, _);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ lseg_append_node(f, l, _v, x, n);
  //@ close llist(list, append(_v, cons(x, nil)));
}


void llist_dispose(struct llist *list)
  //@ requires llist(list, ?v);
  //@ ensures true;
{
  //@ open llist(list, v);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ assert lseg(n, l, v) &*& node(l, _, _);
  while (n != l)
    //@ invariant lseg(n, l, ?rem_v) &*& node(l, _, _);
  {
    //@ open lseg(n, l, rem_v);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(l, l, nil);
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

    //@ open [frac]llist(l, v);
    //@ close [frac/2]llist(l, v);
    //@ close [frac/2]llist(l, v);
    //@ llist_to_llist_with_node_first(l);
    //@ open [frac/2]llist_with_node(l, v, ?first, v);
    f = l->first;
    //@ assert f == first;
    i->current = f;
    //@ close iter(result, frac/2, l, v, v);
    return i;
}


int iter_next(struct iter *i)
    //@ requires iter(i, ?f, ?l, ?v0, ?v) &*& switch (v) { case nil: return false; case cons(h, t): return true; };
    //@ ensures switch (v) { case nil: return false; case cons(h, t): return result == h &*& iter(i, f, l, v0, t); };
{
    //@ open iter(i, f, l, v0, v);
    //@ open [f]llist_with_node(l, v0, i->current, v);
    //@ assert [f]l->first |-> ?lf &*& [f]l->last |-> ?ll &*& [f]lseg2(lf, i->current, ll, ?v1) &*& [f]lseg(i->current, ll, v) &*& [f]node(ll, _, _) &*& v0 == append(v1, v);
    //@ switch(v) { case nil: case cons(h,t): }
    //@ open [f]lseg(i->current, ll, v);
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ lseg2_append_node(lf, c, ll, v1, value, n);
    //@ append_assoc(v1, cons(value, nil), tail(v));
    //@ close [f]llist_with_node(l, v0, n, tail(v));
    //@ close iter(i, f, l, v0, tail(v));
    return value;
}


void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ llist_with_node_to_llist(l);
    free(i);
}


// TODO: make this function pass the verification
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