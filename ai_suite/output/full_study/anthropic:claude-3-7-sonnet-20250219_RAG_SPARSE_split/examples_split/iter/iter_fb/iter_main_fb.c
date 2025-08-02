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
  node->next |-> next &*& node->value |-> value;
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
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
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v);

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
}


void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
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
    
    //@ open [frac]llist(l, v);
    //@ close [frac/2]lseg2(f, f, ?_l, nil);
    //@ close [frac/2]llist_with_node(l, v, f, v);
    //@ close iter(i, frac/2, l, v, v);
    //@ close [frac/2]llist(l, v);
    
    return i;
}


int iter_next(struct iter *i)
    //@ requires iter(i, ?f, ?l, ?v0, ?v) &*& switch (v) { case nil: return false; case cons(h, t): return true; };
    //@ ensures switch (v) { case nil: return false; case cons(h, t): return result == h &*& iter(i, f, l, v0, t); };
{
    //@ open iter(i, f, l, v0, v);
    struct node *c = i->current;
    //@ open [f]llist_with_node(l, v0, c, v);
    //@ open [f]lseg(c, ?_l, v);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close [f]lseg(n, _l, ?t);
    //@ close [f]llist_with_node(l, v0, n, t);
    //@ close iter(i, f, l, v0, t);
    return value;
}


void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ open [f1]llist_with_node(l, v0, ?n, v);
    //@ open [f2]llist(l, v0);
    //@ assert l->first |-> ?f;
    //@ assert l->last |-> ?_l;
    //@ assert [f2]lseg(f, _l, v0);
    //@ assert [f1]lseg2(f, n, _l, ?v1);
    //@ assert [f1]lseg(n, _l, v);
    //@ assert v0 == append(v1, v);
    
    /*@
    // Lemma to merge lseg2 and lseg
    {
        switch (v1) {
            case nil:
                // If v1 is nil, then n == f
                assert n == f;
                // So we already have [f2]lseg(f, _l, v0) and [f1]lseg(f, _l, v)
                // And v0 == v
                break;
            case cons(h, t):
                // We need to merge [f1]lseg2(f, n, _l, v1) and [f1]lseg(n, _l, v)
                // to get [f1]lseg(f, _l, v0)
                open [f1]lseg2(f, n, _l, v1);
                assert f != _l;
                assert [f1]node(f, ?next, h);
                assert [f1]lseg2(next, n, _l, t);
                
                // Recursively merge lseg2(next, n, _l, t) and lseg(n, _l, v)
                // to get lseg(next, _l, append(t, v))
                // Then combine with node(f, next, h) to get lseg(f, _l, cons(h, append(t, v)))
                // which is lseg(f, _l, append(cons(h, t), v)) = lseg(f, _l, append(v1, v)) = lseg(f, _l, v0)
                
                close [f1]lseg(f, _l, v0);
                break;
        }
    }
    @*/
    
    //@ close [f1 + f2]llist(l, v0);
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
    
    //@ assert llist(l, cons(5, cons(10, cons(15, nil))));
    
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    
    //@ assert [1/4]llist(l, cons(5, cons(10, cons(15, nil))));
    //@ assert iter(i1, 1/4, l, cons(5, cons(10, cons(15, nil))), cons(5, cons(10, cons(15, nil))));
    //@ assert iter(i2, 1/4, l, cons(5, cons(10, cons(15, nil))), cons(5, cons(10, cons(15, nil))));
    
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    
    //@ assert iter(i1, 1/4, l, cons(5, cons(10, cons(15, nil))), cons(10, cons(15, nil)));
    
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    
    //@ assert iter(i2, 1/4, l, cons(5, cons(10, cons(15, nil))), cons(10, cons(15, nil)));
    
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    
    //@ assert iter(i1, 1/4, l, cons(5, cons(10, cons(15, nil))), cons(15, nil));
    
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    
    //@ assert iter(i2, 1/4, l, cons(5, cons(10, cons(15, nil))), cons(15, nil));
    
    iter_dispose(i1);
    
    //@ assert [1/2]llist(l, cons(5, cons(10, cons(15, nil))));
    //@ assert iter(i2, 1/4, l, cons(5, cons(10, cons(15, nil))), cons(15, nil));
    
    iter_dispose(i2);
    
    //@ assert [3/4]llist(l, cons(5, cons(10, cons(15, nil))));
    
    llist_dispose(l);
    return 0;
}