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
  n1 == n2 ? v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
@*/

// Helper lemma to join two lsegs
/*@
lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3, list<int> v1, list<int> v2)
  requires lseg(n1, n2, v1) &*& lseg(n2, n3, v2);
  ensures lseg(n1, n3, append(v1, v2));
{
  open lseg(n1, n2, v1);
  if (n1 == n2) {
    // Base case: first segment is empty
    close lseg(n1, n3, append(v1, v2));
  } else {
    // Recursive case: first segment has at least one node
    lseg_append(n1->next, n2, n3, ?t, v2);
    close lseg(n1, n3, append(v1, v2));
  }
}
@*/

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
  //@ ensures llist(list1, append(_v1, _v2));
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  //@ open llist(list1, _v1);
  //@ open llist(list2, _v2);
  
  if (f2 == l2) {
    // Case: list2 has only one node
    //@ open lseg(f2, l2, nil);
    //@ open node(l2, ?l2next, ?l2value);
    
    free(l2);
    free(list2);
    
    //@ close node(l1, l1->next, l1->value);
    //@ close llist(list1, _v1);
  } else {
    // Case: list2 has more than one node
    //@ open lseg(f2, l2, ?tail_v2);
    //@ open node(f2, ?f2next, ?f2value);
    //@ open node(l1, ?l1next, ?l1value);
    
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    //@ close node(l1, f2next, f2value);
    
    // Establish that we now have a segment from list1->first to l2
    //@ assert lseg(list1->first, l1, _v1);
    //@ assert lseg(f2next, l2, tail_v2);
    
    // Connect the segments
    //@ lseg_append(list1->first, l1, l2, _v1, cons(f2value, tail_v2));
    
    free(f2);
    free(list2);
    
    //@ close llist(list1, append(_v1, _v2));
  }
}
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
  n1 == n2 ? v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
@*/

// Helper lemma to join two lsegs
/*@
lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3, list<int> v1, list<int> v2)
  requires lseg(n1, n2, v1) &*& lseg(n2, n3, v2);
  ensures lseg(n1, n3, append(v1, v2));
{
  open lseg(n1, n2, v1);
  if (n1 == n2) {
    // Base case: first segment is empty
    close lseg(n1, n3, append(v1, v2));
  } else {
    // Recursive case: first segment has at least one node
    lseg_append(n1->next, n2, n3, ?t, v2);
    close lseg(n1, n3, append(v1, v2));
  }
}
@*/

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?_v1) &*& llist(list2, ?_v2);
  //@ ensures llist(list1, append(_v1, _v2));
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  //@ open llist(list1, _v1);
  //@ open llist(list2, _v2);
  
  if (f2 == l2) {
    // Case: list2 has only one node (or empty list with sentinel)
    //@ open node(l2, ?l2next, ?l2value);
    
    free(l2);
    free(list2);
    
    //@ close node(l1, l1->next, l1->value);
    //@ close llist(list1, _v1);
  } else {
    // Case: list2 has more than one node
    //@ open lseg(f2, l2, ?tail_v2);
    //@ open node(f2, ?f2next, ?f2value);
    //@ open node(l1, ?l1next, ?l1value);
    
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    //@ close node(l1, f2next, f2value);
    
    // We need to prove that we now have a valid list with values append(_v1, _v2)
    // First, establish that we have a segment from list1->first to l1
    //@ assert lseg(list1->first, l1, _v1);
    
    // Then, establish that we have a segment from l1 to l2 with the values from list2 (except the first node)
    //@ assert lseg(f2next, l2, tail_v2);
    
    // The value of l1 is now f2value, so we need to connect these segments
    //@ lseg_append(list1->first, l1, l1, _v1, nil);
    //@ lseg_append(list1->first, l1, l2, _v1, cons(f2value, tail_v2));
    
    free(f2);
    free(list2);
    
    //@ close llist(list1, append(_v1, _v2));
  }
}
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
  n1 == n2 ? v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
@*/

// Helper lemma to join two lsegs
/*@
lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3, list<int> v1, list<int> v2)
  requires lseg(n1, n2, v1) &*& lseg(n2, n3, v2);
  ensures lseg(n1, n3, append(v1, v2));
{
  open lseg(n1, n2, v1);
  if (n1 == n2) {
    // Base case: first segment is empty
    close lseg(n1, n3, append(v1, v2));
  } else {
    // Recursive case: first segment has at least one node
    lseg_append(n1->next, n2, n3, ?t, v2);
    close lseg(n1, n3, append(v1, v2));
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
    // Case: list2 has only one node (or empty list with sentinel)
    //@ open node(l1, ?l1next, ?l1value);
    //@ open node(l2, ?l2next, ?l2value);
    
    free(l2);
    free(list2);
    
    //@ close node(l1, l1next, l1value);
    //@ close llist(list1, _v1);
  } else {
    // Case: list2 has more than one node
    //@ open lseg(f2, l2, ?tail_v2);
    //@ open node(f2, ?f2next, ?f2value);
    //@ open node(l1, ?l1next, ?l1value);
    
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    //@ close node(l1, f2next, f2value);
    
    // We need to prove that we now have a valid list with values append(_v1, _v2)
    // First, establish that we have a segment from list1->first to l1
    //@ assert lseg(list1->first, l1, _v1);
    
    // Then, establish that we have a segment from f2next to l2 with the tail values from list2
    //@ assert lseg(f2next, l2, tail_v2);
    
    // Now we need to connect these segments through l1
    // First, we need to establish that we have a segment from l1 to l2 with the values [f2value] + tail_v2
    //@ close lseg(l1, f2next, cons(f2value, nil));
    //@ lseg_append(l1, f2next, l2, cons(f2value, nil), tail_v2);
    
    // Now we can connect the segment from list1->first to l1 with the segment from l1 to l2
    //@ lseg_append(list1->first, l1, l2, _v1, cons(f2value, tail_v2));
    
    free(f2);
    free(list2);
    
    //@ close llist(list1, append(_v1, _v2));
  }
}
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
  n1 == n2 ? v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _);
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
    // Case: list2 has only one node (or empty list with sentinel)
    //@ open node(l1, ?l1next, ?l1value);
    //@ open node(l2, ?l2next, ?l2value);
    
    free(l2);
    free(list2);
    
    //@ close node(l1, l1next, l1value);
    //@ close llist(list1, _v1);
    //@ assert _v1 == append(_v1, nil);
  } else {
    // Case: list2 has more than one node
    //@ open lseg(f2, l2, ?tail_v2);
    //@ open node(f2, ?f2next, ?f2value);
    //@ open node(l1, ?l1next, ?l1value);
    
    l1->next = f2->next;