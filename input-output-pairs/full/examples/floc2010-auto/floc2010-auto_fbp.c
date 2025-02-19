#include "stdlib.h"

struct node {
  int value;
  struct node *next;
};

/*@
predicate node(struct node *n; int value, struct node *next) =
  n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);
@*/

struct node *create_node(int value, struct node *next)
  //@ requires emp;
  //@ ensures node(result, value, next);
{
  struct node *n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->value = value;
  n->next = next;
  return n;
}

struct list {
  struct node *first;
  struct node *last;
};

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> vs) =
  n1 == n2 ? vs == nil : node(n1, ?h, ?next) &*& lseg(next, n2, ?t) &*& vs == cons(h, t);

predicate list(struct list *l; list<int> vs) =
  l->first |-> ?fn &*& l->last |-> ?ln &*& lseg(fn, ln, vs) &*& node(ln, _, _) &*& malloc_block_list(l);
@*/

struct list *create_list()
  //@ requires emp;
  //@ ensures list(result, nil);
{
  struct list *l = malloc(sizeof(struct list));
  if(l == 0) abort();
  struct node* n = create_node(0, 0);
  l->first = n;
  l->last = n;
  return l;
}

int list_length_helper(struct node *n1, struct node *n2)
  //@ requires lseg(n1, n2, ?vs) &*& node(n2, _, _) &*& length(vs) <= INT_MAX;
  //@ ensures lseg(n1, n2, vs) &*& node(n2, _, _) &*& result == length(vs);
{
  int len;
  if(n1 == n2) {
    len = 0;
  } else {
    len = list_length_helper(n1->next, n2);
    len = len + 1;
  }
  return len;
}

int list_length(struct list *l)
  //@ requires list(l, ?vs) &*& length(vs) <= INT_MAX;
  //@ ensures list(l, vs);
{
  return list_length_helper(l->first, l->last);
}


/*@
fixpoint list<int> add(list<int> l, int x)
{
  switch(l) {
    case nil: return cons(x, nil);
    case cons(h, t): return cons(h, add(t, x));
  }
}
@*/

void list_add(struct list *l, int x)
  //@ requires list(l, ?vs);
  //@ ensures list(l, add(vs, x));
{
  struct node *n = create_node(0, 0);
  struct node *nl = l->last;
  nl->next = n;
  nl->value = x;
  l->last = n;
}