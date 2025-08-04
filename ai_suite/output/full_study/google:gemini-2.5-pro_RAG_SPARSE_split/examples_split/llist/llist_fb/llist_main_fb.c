#include "stdlib.h"
#include "assert.h"
#include "limits.h"

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
  list->first |-> ?_f &*& list->last |-> ?_l &*& malloc_block_llist(list) &*& lseg(_f, _l, v) &*& node(_l, _, _);
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

/*@
lemma void lseg_append_node(struct node* n1, struct node* n2)
  requires lseg(n1, n2, ?v) &*& node(n2, ?n3, ?val);
  ensures lseg(n1, n3, append(v, cons(val, nil)));
{
  open lseg(n1, n2, v);
  if (n1 == n2) {
    close lseg(n3, n3, nil);
    close lseg(n1, n3, cons(val, nil));
  } else {
    lseg_append_node(n1->next, n2);
    close lseg(n1, n3, append(v, cons(val, nil)));
  }
}

lemma void lseg_append_lseg(struct node* n1, struct node* n2, struct node* n3)
  requires lseg(n1, n2, ?v1) &*& lseg(n2, n3, ?v2);
  ensures lseg(n1, n3, append(v1, v2));
{
  open lseg(n1, n2, v1);
  if (n1 != n2) {
    lseg_append_lseg(n1->next, n2, n3);
    close lseg(n1, n3, append(v1, v2));
  }
}
@*/

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?_v);
  //@ ensures llist(list, append(_v, cons(x, nil)));
{
  //@ open llist(list, _v);
  //@ list->first |-> ?f &*& list->last |-> ?l_old &*& lseg(f, l_old, _v) &*& node(l_old, _, _);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ lseg_append_node(f, l);
  //@ close llist(list, append(_v, cons(x, nil)));
}


void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
  //@ ensures llist(list1, append(_v1, _v2));
{
  //@ open llist(list1, _v1);
  //@ list1->first |-> ?f1 &*& list1->last |-> ?l1_node &*& lseg(f1, l1_node, _v1) &*& node(l1_node, _, _);
  //@ open llist(list2, _v2);
  //@ list2->first |-> ?f2_node &*& list2->last |-> ?l2_node &*& lseg(f2_node, l2_node, _v2) &*& node(l2_node, _, _);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    //@ assert _v2 == nil;
    free(l2);
    free(list2);
    //@ append_nil(_v1);
    //@ close llist(list1, _v1);
  } else {
    //@ open lseg(f2, l2, _v2);
    //@ assert node(f2, ?f2_next, ?f2_val) &*& lseg(f2_next, l2, ?_v2_tail) &*& _v2 == cons(f2_val, _v2_tail);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ lseg_append_node(f1, l1);
    //@ lseg_append_lseg(f1, f2->next, l2);
    //@ append_assoc(_v1, cons(f2_val, nil), _v2_tail);
    //@ close llist(list1, append(_v1, _v2));
  }
}


void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  //@ open llist(list, _);
  //@ list->first |-> ?f &*& list->last |-> ?l_node;
  //@ open lseg(f, l_node, _);
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
  free(l);
  free(list);
}


int llist_length_iterative(struct llist *list)
  //@ requires [?frac]llist(list, ?_v);
  //@ ensures [frac]llist(list, _v) &*& result == length(_v);
{
  //@ open [frac]llist(list, _v);
  //@ list->first |-> ?f &*& list->last |-> ?l;
  struct node *n = list->first;
  int c = 0;
  while (n != list->last)
    //@ invariant [frac]lseg(f, n, ?v_done) &*& [frac]lseg(n, l, ?v_rem) &*& _v == append(v_done, v_rem) &*& c == length(v_done);
  {
    //@ open [frac]lseg(n, l, v_rem);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ close [frac]lseg(f, n, append(v_done, cons(head(v_rem), nil)));
    //@ append_assoc(v_done, cons(head(v_rem), nil), tail(v_rem));
  }
  //@ open [frac]lseg(l, l, ?v_rem);
  //@ assert v_rem == nil;
  //@ close [frac]llist(list, _v);
  return c;
}


int llist_length_recursive_helper(struct node *n1, struct node *n2)
  //@ requires lseg(n1, n2, ?vs) &*& node(n2, _, _);
  //@ ensures lseg(n1, n2, vs) &*& node(n2, _, _) &*& result == length(vs);
{
  //@ open lseg(n1, n2, vs);
  int len;
  if(n1 == n2) {
    len = 0;
  } else {
    len = llist_length_recursive_helper(n1->next, n2);
    len = len + 1;
  }
  //@ close lseg(n1, n2, vs);
  return len;
}


int llist_length_recursive(struct llist *l)
  //@ requires llist(l, ?vs);
  //@ ensures llist(l, vs) &*& result == length(vs);
{
  //@ open llist(l, vs);
  int len = llist_length_recursive_helper(l->first, l->last);
  //@ close llist(l, vs);
  return len;
}


int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _v);
  //@ list->first |-> ?f &*& list->last |-> ?l;
  struct node *n = list->first;
  int i = 0;
  while (i < index)
    //@ invariant 0 <= i &*& i <= index &*& lseg(f, n, take(i, _v)) &*& lseg(n, l, drop(i, _v));
  {
    //@ open lseg(n, l, drop(i, _v));
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ close lseg(f, n, take(i, _v));
  }
  //@ open lseg(n, l, drop(index, _v));
  int value = n->value;
  //@ close lseg(n, l, drop(index, _v));
  //@ lseg_append_lseg(f, n, l);
  //@ append_take_drop_n(_v, index);
  //@ close llist(list, _v);
  return value;
}


int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?v) &*& v != nil;
  //@ ensures llist(l, ?t) &*& v == cons(result, t);
{
  //@ open llist(l, v);
  //@ list->first |-> ?f &*& list->last |-> ?last;
  //@ open lseg(f, last, v);
  struct node *nf = l->first;
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