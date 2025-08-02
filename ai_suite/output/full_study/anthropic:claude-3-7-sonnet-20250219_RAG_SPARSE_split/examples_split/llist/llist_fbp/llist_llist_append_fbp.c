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
lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3, list<int> v1, list<int> v2)
  requires lseg(n1, n2, v1) &*& lseg(n2, n3, v2);
  ensures lseg(n1, n3, append(v1, v2));
{
  open lseg(n1, n2, v1);
  if (n1 == n2) {
    // Base case: n1 == n2, so v1 is empty
    close lseg(n1, n3, append(nil, v2));
  } else {
    // Recursive case: n1 != n2
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
  
  //@ open node(l1, ?l1_next, ?l1_value);
  
  if (f2 == l2) {
    // Case: list2 is empty (only has sentinel node)
    //@ open lseg(f2, l2, _v2);
    //@ assert _v2 == nil;
    
    free(l2);
    free(list2);
    
    //@ close node(l1, l1_next, l1_value);
    //@ close llist(list1, _v1);
  } else {
    // Case: list2 is not empty
    //@ open node(f2, ?f2_next, ?f2_value);
    
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    //@ close node(l1, f2_next, f2_value);
    //@ open lseg(f2, l2, _v2);
    //@ assert _v2 == cons(f2_value, ?t2);
    //@ lseg_append(list1->first, l1, l2, _v1, t2);
    
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
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
@*/

/*@
lemma void lseg_append(struct node *n1, struct node *n2, struct node *n3, list<int> v1, list<int> v2)
  requires lseg(n1, n2, v1) &*& lseg(n3, 0, v2) &*& n2->next |-> n3;
  ensures lseg(n1, 0, append(v1, v2)) &*& n2->next |-> n3;
{
  open lseg(n1, n2, v1);
  if (n1 == n2) {
    // Base case: n1 == n2, so v1 is empty
  } else {
    // Recursive case: n1 != n2
    open node(n1, ?next, ?value);
    lseg_append(next, n2, n3, ?tail, v2);
    close node(n1, next, value);
    close lseg(n1, 0, append(v1, v2));
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
  
  //@ open node(l1, ?l1_next, ?l1_value);
  
  if (f2 == l2) {
    // Case: list2 is empty (only has sentinel node)
    //@ assert _v2 == nil;
    //@ assert append(_v1, nil) == _v1;
    
    free(l2);
    free(list2);
    
    //@ close node(l1, l1_next, l1_value);
    //@ close llist(list1, _v1);
  } else {
    // Case: list2 is not empty
    //@ open lseg(f2, l2, _v2);
    //@ open node(f2, ?f2_next, ?f2_value);
    
    l1->next = f2_next;
    l1->value = f2_value;
    list1->last = l2;
    
    //@ close node(l1, f2_next, f2_value);
    //@ assert _v2 == cons(f2_value, ?t2);
    //@ assert lseg(f2_next, l2, t2);
    //@ close lseg(l1, l2, cons(f2_value, t2));
    //@ close llist(list1, append(_v1, _v2));
    
    free(f2);
    free(list2);
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
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
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
    // Case: list2 is empty (only has sentinel node)
    //@ assert _v2 == nil;
    //@ assert append(_v1, nil) == _v1;
    
    //@ open node(l1, ?l1_next, ?l1_value);
    //@ open node(l2, ?l2_next, ?l2_value);
    
    free(l2);
    free(list2);
    
    //@ close node(l1, l1_next, l1_value);
    //@ close llist(list1, _v1);
  } else {
    // Case: list2 is not empty
    //@ open node(l1, ?l1_next, ?l1_value);
    //@ open lseg(f2, l2, _v2);
    //@ open node(f2, ?f2_next, ?f2_value);
    
    l1->next = f2_next;
    l1->value = f2_value;
    list1->last = l2;
    
    //@ close node(l1, f2_next, f2_value);
    
    free(f2);
    free(list2);
    
    //@ assert _v2 == cons(f2_value, ?t2);
    //@ assert lseg(f2_next, l2, t2);
    
    /*@
    lemma void append_nil_right<t>(list<t> xs)
      requires true;
      ensures append(xs, nil) == xs;
    {
      switch(xs) {
        case nil: 
        case cons(h, t): append_nil_right(t);
      }
    }
    
    lemma void append_cons<t>(list<t> xs, t x, list<t> ys)
      requires true;
      ensures append(xs, cons(x, ys)) == append(append(xs, cons(x, nil)), ys);
    {
      switch(xs) {
        case nil: 
        case cons(h, t): append_cons(t, x, ys);
      }
    }
    @*/
    
    //@ append_cons(_v1, f2_value, t2);
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
  node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *n1, struct node *n2; list<int> v) =
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t) &*& v == cons(h, t);

predicate llist(struct llist *list; list<int> v) =
  list->first |-> ?_f &*& list->last |-> ?_l &*& lseg(_f, _l, v) &*& node(_l, _, _) &*& malloc_block_llist(list);
@*/

/*@
lemma void append_nil_right<t>(list<t> xs)
  requires true;
  ensures append(xs, nil) == xs;
{
  switch(xs) {
    case nil: 
    case cons(h, t): append_nil_right(t);
  }
}

lemma void append_cons<t>(list<t> xs, t x, list<t> ys)
  requires true;
  ensures append(xs, cons(x, ys)) == append(append(xs, cons(x, nil)), ys);
{
  switch(xs) {
    case nil: 
    case cons(h, t): append_cons(t, x, ys);
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
    // Case: list2 is empty (only has sentinel node)
    //@ assert _v2 == nil;
    //@ append_nil_right(_v1);
    
    //@ open node(l1, ?l1_next, ?l1_value);
    //@ open node(l2, ?l2_next, ?l2_value);
    
    free(l2);
    free(list2);
    
    //@ close node(l1, l1_next, l1_value);
    //@ close llist(list1, _v1);
  } else {
    // Case: list2 is not empty
    //@ open node(l1, ?l1_next, ?l1_value);
    //@ open lseg(f2, l2, _v2);
    //@ open node(f2, ?f2_next, ?f2_value);
    
    l1->next = f2_next;
    l1->value = f2_value;
    list1->last = l2;
    
    //@ close node(l1, f2_next, f2_value);
    
    free(f2);
    free(list2);
    
    //@ assert _v2 == cons(f2_value, ?t2);
    //@ assert lseg(f2_next, l2, t2);
    
    /*@
    lemma void lseg_append(struct node *n1, struct node *n2