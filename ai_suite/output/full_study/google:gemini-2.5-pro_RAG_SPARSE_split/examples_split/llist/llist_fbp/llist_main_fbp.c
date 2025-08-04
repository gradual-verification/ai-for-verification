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
  //@ open llist(list, _v);
  l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ lseg_append_node(list->first, l);
  //@ close llist(list, append(_v, cons(x, nil)));
}

/*@
lemma void lseg_append_node(struct node* f, struct node* l)
  requires lseg(f, l, ?vs) &*& node(l, ?n, ?v);
  ensures lseg(f, n, append(vs, cons(v, nil)));
{
  open lseg(f, l, vs);
  if (f == l) {
    close lseg(f, n, cons(v, nil));
  } else {
    lseg_append_node(f->next, l);
    close lseg(f, n, append(vs, cons(v, nil)));
  }
}
@*/

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
  //@ ensures llist(list1, append(_v1, _v2));
{
  //@ open llist(list1, _v1);
  //@ open llist(list2, _v2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    //@ open lseg(f2, l2, _v2);
    //@ open node(l2, _, _);
    free(l2);
    free(list2);
    //@ append_nil(_v1);
    //@ close llist(list1, _v1);
  } else {
    //@ open lseg(f2, l2, _v2);
    //@ open node(f2, _, _);
    //@ open node(l1, _, _);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ close lseg(l1, f2->next, cons(f2->value, nil));
    //@ lseg_append(list1->first, l1);
    //@ lseg_append(l1, f2->next);
    //@ append_assoc(_v1, cons(f2->value, nil), tail(_v2));
    //@ close llist(list1, append(_v1, _v2));
  }
}

/*@
lemma void lseg_append(struct node* n1, struct node* n2)
  requires lseg(n1, n2, ?v1) &*& lseg(n2, ?n3, ?v2);
  ensures lseg(n1, n3, append(v1, v2));
{
  open lseg(n1, n2, v1);
  if (n1 == n2) {
  } else {
    lseg_append(n1->next, n2);
    close lseg(n1, n3, append(v1, v2));
  }
}
@*/

void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  //@ open llist(list, ?v);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, _);
  {
    //@ open lseg(n, l, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(l, l, _);
  //@ open node(l, _, _);
  free(l);
  free(list);
}


int llist_length_iterative(struct llist *list)
  //@ requires [?frac]llist(list, ?_v);
  //@ ensures [frac]llist(list, _v) &*& result == length(_v);
{
  //@ open [frac]llist(list, _v);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ lseg_split(f, n);
  while (n != l)
    /*@
    invariant
      [frac]lseg(f, n, ?v_done) &*& [frac]lseg(n, l, ?v_rem) &*&
      _v == append(v_done, v_rem) &*& c == length(v_done) &*&
      [frac]node(l, _, _) &*& [frac]list->first |-> f &*& [frac]list->last |-> l &*& [frac]malloc_block_llist(list);
    @*/
  {
    //@ open [frac]lseg(n, l, v_rem);
    //@ open [frac]node(n, _, _);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ lseg_append(f, n);
    //@ append_assoc(v_done, cons(head(v_rem), nil), tail(v_rem));
  }
  //@ lseg_append(f, l);
  //@ close [frac]llist(list, _v);
  return c;
}

/*@
lemma void lseg_split(struct node* n1, struct node* n2)
  requires [?f]lseg(n1, ?n3, ?v) &*& mem(n2, lseg_nodes(n1, n3));
  ensures [f]lseg(n1, n2, ?v1) &*& [f]lseg(n2, n3, ?v2) &*& v == append(v1, v2) &*& length(v1) == index_of(n2, lseg_nodes(n1, n3));
{
  open [f]lseg(n1, n3, v);
  if (n1 == n2) {
    close [f]lseg(n1, n2, nil);
  } else {
    lseg_split(n1->next, n2);
    close [f]lseg(n1, n2, _);
  }
}

fixpoint list<struct node*> lseg_nodes(struct node* n1, struct node* n2)
  requires lseg(n1, n2, _);
{
  open lseg(n1, n2, _);
  return n1 == n2 ? nil : cons(n1, lseg_nodes(n1->next, n2));
}
@*/

int llist_length_recursive_helper(struct node *n1, struct node *n2)
  //@ requires lseg(n1, n2, ?vs) &*& node(n2, _, _) &*& length(vs) <= INT_MAX;
  //@ ensures lseg(n1, n2, vs) &*& node(n2, _, _) &*& result == length(vs);
{
  int len;
  //@ open lseg(n1, n2, vs);
  if(n1 == n2) {
    len = 0;
  } else {
    //@ open node(n1, _, _);
    len = llist_length_recursive_helper(n1->next, n2);
    if (len == INT_MAX) abort();
    len = len + 1;
  }
  //@ close lseg(n1, n2, vs);
  return len;
}


int llist_length_recursive(struct llist *l)
  //@ requires llist(l, ?vs) &*& length(vs) <= INT_MAX;
  //@ ensures llist(l, vs) &*& result == length(vs);
{
  //@ open llist(l, vs);
  int result = llist_length_recursive_helper(l->first, l->last);
  //@ close llist(l, vs);
  return result;
}


int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ lseg_split(f, n);
  while (i < index)
    /*@
    invariant
      0 <= i &*& i <= index &*&
      lseg(f, n, take(i, _v)) &*& lseg(n, l, drop(i, _v)) &*&
      node(l, _, _) &*& list->first |-> f &*& list->last |-> l &*& malloc_block_llist(list);
    @*/
  {
    //@ open lseg(n, l, drop(i, _v));
    //@ open node(n, _, _);
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ lseg_append(f, n);
  }
  //@ open lseg(n, l, drop(index, _v));
  //@ open node(n, _, _);
  int value = n->value;
  //@ close lseg(n, l, drop(index, _v));
  //@ lseg_append(f, n);
  //@ close llist(list, _v);
  return value;
}


int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?v) &*& v != nil;
  //@ ensures llist(l, ?t) &*& v == cons(result, t);
{
  //@ open llist(l, v);
  struct node *nf = l->first;
  //@ open lseg(nf, l->last, v);
  //@ open node(nf, _, _);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(v));
  return nfv;
}


// TODO: make this function pass the verification
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
  int x = llist_removeFirst(l2);
  assert(x == 40);
  llist_append(l1, l2);
  int n1 = llist_length_iterative(l1);
  assert(n1 == 5);
  int n2 = llist_length_recursive(l1);
  assert(n2 == 5);
  int e0 = llist_lookup(l1, 0);
  assert(e0 == 10);
  int e1 = llist_lookup(l1, 1);
  assert(e1 == 20);
  int e2 = llist_lookup(l1, 2);
  assert(e2 == 30);
  int e3 = llist_lookup(l1, 3);
  assert(e3 == 50);
  int e4 = llist_lookup(l1, 4);
  assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}