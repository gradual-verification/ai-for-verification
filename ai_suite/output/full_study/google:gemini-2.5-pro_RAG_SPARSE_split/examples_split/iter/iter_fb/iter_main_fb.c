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
  n1 == n2 ? v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*& lseg(_f, _l, v) &*& node(_l, 0, 0);
@*/

/*@

predicate lseg2(struct node *first, struct node *last, struct node *final, list<int> v;) =
  first == last ? v == nil :
    first != final &*& node(first, ?next, ?head) &*& lseg2(next, last, final, ?tail) &*& v == cons(head, tail);
@*/


struct iter {
    struct node *current;
};

/*@

predicate llist_with_node(struct llist *list, list<int> v0, struct node *n, list<int> vn) =
  list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*& lseg2(f, n, l, ?v1) &*& lseg(n, l, vn) &*& node(l, 0, 0) &*& v0 == append(v1, vn);

predicate iter(struct iter *i, real frac, struct llist *l, list<int> v0, list<int> v) =
  i->current |-> ?n &*& malloc_block_iter(i) &*& [frac]llist_with_node(l, v0, n, v);

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
  //@ close node(n, 0, 0);
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}


void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  //@ open llist(list, _v);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  //@ open node(l, 0, 0);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(n, 0, 0);
  //@ close lseg(n, n, nil);
  //@ close node(l, n, x);
  //@ lseg_add_node(list->first, l);
  //@ close llist(list, append(_v, cons(x, nil)));
}

/*@
lemma void lseg_add_node(struct node* first, struct node* last)
  requires lseg(first, last, ?v) &*& node(last, ?next, ?val) &*& lseg(next, next, nil);
  ensures lseg(first, next, append(v, cons(val, nil)));
{
  open lseg(first, last, v);
  if (first == last) {
    close lseg(first, next, cons(val, nil));
  } else {
    lseg_add_node(first->next, last);
    close lseg(first, next, append(v, cons(val, nil)));
  }
}
@*/


void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  //@ open llist(list, _);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, _) &*& node(l, 0, 0);
  {
    //@ open lseg(n, l, _);
    //@ open node(n, _, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(l, l, _);
  //@ open node(l, 0, 0);
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
    f = l->first;
    i->current = f;
    //@ close lseg2(f, f, l->last, nil);
    //@ close [frac/2]llist_with_node(l, v, f, v);
    //@ close iter(i, frac/2, l, v, v);
    //@ close [frac/2]llist(l, v);
    return i;
}


int iter_next(struct iter *i)
    //@ requires iter(i, ?f, ?l, ?v0, ?v) &*& v != nil;
    //@ ensures result == head(v) &*& iter(i, f, l, v0, tail(v));
{
    //@ open iter(i, f, l, v0, v);
    //@ open [f]llist_with_node(l, v0, i->current, v);
    //@ open lseg(i->current, l->last, v);
    //@ open node(i->current, _, _);
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close [f]lseg2(l->first, n, l->last, append(head(v0) == 0 ? nil : take(length(v0) - length(v), v0), cons(value, nil)));
    //@ close [f]llist_with_node(l, v0, n, tail(v));
    //@ close iter(i, f, l, v0, tail(v));
    return value;
}


void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ open [f1]llist_with_node(l, v0, i->current, v);
    //@ lseg2_plus_lseg(l->first, i->current, l->last);
    free(i);
    //@ open [f2]llist(l, v0);
    //@ close [f1+f2]llist(l, v0);
}

/*@
lemma void lseg2_plus_lseg(struct node *first, struct node *mid, struct node *last)
    requires [?f]lseg2(first, mid, last, ?v1) &*& [?f]lseg(mid, last, ?v2);
    ensures [f]lseg(first, last, append(v1, v2));
{
    open [f]lseg2(first, mid, last, v1);
    if (first == mid) {
    } else {
        lseg2_plus_lseg(first->next, mid, last);
        close [f]lseg(first, last, append(v1, v2));
    }
}

lemma void lseg_split(struct node *first, struct node *mid, struct node *last)
    requires [?f]lseg(first, last, ?v) &*& v == append(?v1, ?v2) &*& length(v1) == ?len &*& lseg2(first, mid, last, v1);
    ensures [f]lseg2(first, mid, last, v1) &*& [f]lseg(mid, last, v2);
{
    open lseg2(first, mid, last, v1);
    if (first == mid) {
        close [f]lseg2(first, mid, last, v1);
    } else {
        open [f]lseg(first, last, v);
        lseg_split(first->next, mid, last);
        close [f]lseg2(first, mid, last, v1);
    }
}

lemma void llist_with_node_to_llist(struct llist *l)
    requires [?f]llist_with_node(l, ?v0, ?n, ?vn);
    ensures [f]llist(l, v0);
{
    open [f]llist_with_node(l, v0, n, vn);
    lseg2_plus_lseg(l->first, n, l->last);
    close [f]llist(l, v0);
}

lemma void llist_to_llist_with_node(struct llist *l, struct node *n, list<int> v1, list<int> vn)
    requires [?f]llist(l, ?v0) &*& v0 == append(v1, vn) &*& lseg2(l->first, n, l->last, v1);
    ensures [f]llist_with_node(l, v0, n, vn);
{
    open [f]llist(l, v0);
    lseg_split(l->first, n, l->last);
    close [f]llist_with_node(l, v0, n, vn);
}
@*/

// TODO: make this function pass the verification
int main()
    //@ requires true;
    //@ ensures true;
{
    struct llist *l = create_llist();
    llist_add(l, 5);
    llist_add(l, 10);
    llist_add(l, 15);
    
    //@ list<int> v = cons(5, cons(10, cons(15, nil)));
    
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    
    //@ list<int> v_after_1 = cons(10, cons(15, nil));
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    
    //@ list<int> v_after_2 = cons(15, nil);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    
    //@ open iter(i2, 0.25, l, v, v_after_2);
    //@ struct node *n2 = i2->current;
    //@ llist_with_node_to_llist(l);
    
    iter_dispose(i1);
    
    //@ list<int> v1_for_n2 = cons(5, cons(10, nil));
    //@ open llist(l, v);
    //@ struct node *first = l->first;
    //@ struct node *last = l->last;
    //@ open lseg(first, last, v);
    //@ open node(first, ?n1_node, 5);
    //@ open lseg(n1_node, last, v_after_1);
    //@ open node(n1_node, ?n2_node, 10);
    //@ assert n2 == n2_node;
    //@ close lseg2(n2, n2, last, nil);
    //@ close node(n1_node, n2, 10);
    //@ close lseg2(n1_node, n2, last, cons(10, nil));
    //@ close node(first, n1_node, 5);
    //@ close lseg2(first, n2, last, v1_for_n2);
    //@ close lseg(n1_node, last, v_after_1);
    //@ close lseg(first, last, v);
    //@ close llist(l, v);
    
    //@ llist_to_llist_with_node(l, n2, v1_for_n2, v_after_2);
    //@ close iter(i2, 0.25, l, v, v_after_2);
    
    iter_dispose(i2);
    
    llist_dispose(l);
    return 0;
}