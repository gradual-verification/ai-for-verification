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
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, _v);
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(n, 0, 0);
  //@ open node(l, _, _);
  //@ close node(l, n, x);
  
  /*@
  {
    open lseg(list->first, l, _v);
    if (list->first == l) {
      close lseg(n, n, nil);
      close lseg(list->first, n, cons(x, nil));
    } else {
      open node(list->first, ?next_first, ?val_first);
      close node(list->first, next_first, val_first);
      
      // Lemma to extend the lseg
      struct node *curr = list->first;
      list<int> prefix = nil;
      while (curr != l)
        invariant lseg(list->first, curr, prefix) &*& node(curr, ?next_curr, ?val_curr) &*& 
                  lseg(next_curr, l, ?suffix) &*& _v == append(prefix, cons(val_curr, suffix));
        decreases length(suffix);
      {
        open node(curr, ?next, ?val);
        open lseg(next, l, suffix);
        
        if (next == l) {
          close lseg(n, n, nil);
          close lseg(next, n, cons(x, nil));
          close node(curr, next, val);
          close lseg(list->first, n, append(prefix, cons(val, cons(x, nil))));
          assert append(prefix, cons(val, cons(x, nil))) == append(_v, cons(x, nil));
          break;
        } else {
          prefix = append(prefix, cons(val, nil));
          curr = next;
          close node(curr, ?next_curr, ?val_curr);
        }
      }
    }
  }
  @*/
  
  //@ close llist(list, append(_v, cons(x, nil)));
}


void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  //@ open llist(list, _);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant lseg(n, l, _) &*& node(l, _, _);
  {
    //@ open lseg(n, l, _);
    struct node *next = n->next;
    //@ open node(n, _, _);
    free(n);
    n = next;
  }
  //@ open node(l, _, _);
  free(l);
  free(list);
}


int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?v) &*& v != nil;
  //@ ensures llist(l, ?t) &*& v == cons(result, t);
{
  //@ open llist(l, v);
  struct node *nf = l->first;
  //@ open lseg(nf, l->last, v);
  //@ open node(nf, ?nfn, ?nfv);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(v));
  return nfv;
}


// TODO: make this function pass the verification
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
  //@ assert x1 == 10;
  int x2 = llist_removeFirst(l);
  //@ assert x2 == 20;
  llist_dispose(l);
}