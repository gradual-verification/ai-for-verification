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
  
lemma void distinct_nodes(struct node *n1, struct node *n2)
  requires node(n1, ?v1, ?nn1) &*& node(n2, ?v2, ?nn2);
  ensures node(n1, v1, nn1) &*& node(n2, v2, nn2) &*& n1 != n2;
{
  open node(n1, _, _);
  open node(n2, _, _);
  close node(n1, v1, nn1);
  close node(n2, v2, nn2);  
}
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
  //@ open lseg(n1, n2, vs);
  if(n1 == n2) {
    //@ if (n1 != n2) pointer_fractions_same_address(&n1->next, &n2->next);
    len = 0;
  } else {
    //@ open node(n1, ?n1v, ?n1n);
    len = list_length_helper(n1->next, n2);
    len = len + 1;
   //@ close node(n1, n1v, n1n);
  }
  //@ close lseg(n1, n2, vs); 
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

lemma void add_lemma(struct node *n1)
  requires lseg(n1, ?n2, ?vs) &*& node(n2, ?v, ?n3) &*& node(n3, _, _);
  ensures lseg(n1, n3, add(vs, v)) &*& node(n3, _, _);
{
  distinct_nodes(n2, n3);
  open lseg(n1, n2, vs);
  if(n1 == n2) {
  } else {
    distinct_nodes(n1, n3);
    add_lemma(n1->next);
  }
  close lseg(n1, n3, add(vs, v));
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
  //@ add_lemma(l->first);
}