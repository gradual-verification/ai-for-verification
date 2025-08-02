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
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

@*/

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ open [f1]llist_with_node(l, v0, ?n, v);
    
    /*@
    // We need to convert llist_with_node back to llist
    // First, we need to show that lseg2 + lseg = lseg
    // Let's start by getting the components
    assert l->first |-> ?f;
    assert l->last |-> ?last;
    assert lseg2(f, n, last, ?v1);
    assert lseg(n, last, v);
    assert v0 == append(v1, v);
    
    // Now we need to convert lseg2 + lseg to lseg
    // We'll use a recursive approach based on the structure of v1
    if (v1 == nil) {
        // If v1 is empty, then f == n, and we already have lseg(n, last, v)
        assert f == n;
        assert lseg(f, last, v);
    } else {
        // If v1 is not empty, we need to build up lseg(f, last, v0)
        // We know lseg2(f, n, last, v1) and lseg(n, last, v)
        // We need to convert this to lseg(f, last, append(v1, v))
        
        // Open lseg2 to get the first node
        open lseg2(f, n, last, v1);
        assert node(f, ?next, ?head);
        assert lseg2(next, n, last, ?tail);
        assert v1 == cons(head, tail);
        
        // Now we need to build lseg(f, last, append(v1, v))
        // We know lseg(n, last, v) and we need to build lseg(f, last, cons(head, append(tail, v)))
        close lseg(f, last, append(v1, v));
    }
    
    // Now we can combine the fractions
    @*/
    
    free(i);
    
    //@ close [f1 + f2]llist(l, v0);
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
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

// Helper lemma to convert lseg2 + lseg to lseg
lemma void lseg2_lseg_to_lseg(struct node *first, struct node *mid, struct node *last, list<int> v1, list<int> v2)
  requires lseg2(first, mid, last, v1) &*& lseg(mid, last, v2);
  ensures lseg(first, last, append(v1, v2));
{
  switch(v1) {
    case nil:
      // If v1 is empty, then first == mid, and we already have lseg(mid, last, v2)
      open lseg2(first, mid, last, nil);
      assert first == mid;
      // We already have lseg(mid, last, v2), which is lseg(first, last, v2)
      // And append(nil, v2) == v2
    case cons(h, t):
      // If v1 is not empty, we need to build up lseg(first, last, append(v1, v2))
      open lseg2(first, mid, last, v1);
      assert first != last;
      assert node(first, ?next, h);
      assert lseg2(next, mid, last, t);
      
      // Recursive call to handle the rest of the list
      lseg2_lseg_to_lseg(next, mid, last, t, v2);
      assert lseg(next, last, append(t, v2));
      
      // Now we can build lseg(first, last, append(v1, v2))
      close lseg(first, last, append(v1, v2));
  }
}

@*/

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ open [f1]llist_with_node(l, v0, ?n, v);
    
    /*@
    // We need to convert llist_with_node back to llist
    // First, we need to show that lseg2 + lseg = lseg
    assert l->first |-> ?f;
    assert l->last |-> ?last;
    assert lseg2(f, n, last, ?v1);
    assert lseg(n, last, v);
    assert v0 == append(v1, v);
    
    // Use our helper lemma to convert lseg2 + lseg to lseg
    lseg2_lseg_to_lseg(f, n, last, v1, v);
    assert lseg(f, last, v0);
    
    // Now we can combine the fractions
    @*/
    
    free(i);
    
    //@ close [f1]llist(l, v0);
    //@ close [f1 + f2]llist(l, v0);
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
  i->current |-> ?n &*& [frac]llist_with_node(l, v0, n, v) &*& malloc_block_iter(i);

// Helper lemma to convert lseg2 + lseg to lseg
lemma void lseg2_lseg_to_lseg(struct node *first, struct node *mid, struct node *last, list<int> v1, list<int> v2)
  requires lseg2(first, mid, last, v1) &*& lseg(mid, last, v2);
  ensures lseg(first, last, append(v1, v2));
{
  switch(v1) {
    case nil:
      open lseg2(first, mid, last, nil);
    case cons(h, t):
      open lseg2(first, mid, last, cons(h, t));
      lseg2_lseg_to_lseg(next, mid, last, t, v2);
      close lseg(first, last, append(cons(h, t), v2));
  }
}

@*/

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f1, ?l, ?v0, ?v) &*& [?f2]llist(l, v0);
    //@ ensures [f1 + f2]llist(l, v0);
{
    //@ open iter(i, f1, l, v0, v);
    //@ assert i->current |-> ?n;
    //@ assert [f1]llist_with_node(l, v0, n, v);
    //@ assert malloc_block_iter(i);
    
    //@ open [f2]llist(l, v0);
    //@ assert l->first |-> ?_f;
    //@ assert l->last |-> ?_l;
    //@ assert [f2]lseg(_f, _l, v0);
    //@ assert [f2]node(_l, _, _);
    
    //@ open [f1]llist_with_node(l, v0, n, v);
    //@ assert [f1]list->first |-> ?f;
    //@ assert [f1]list->last |-> ?last;
    //@ assert [f1]malloc_block_llist(list);
    //@ assert [f1]lseg2(f, n, last, ?v1);
    //@ assert [f1]lseg(n, last, v);
    //@ assert [f1]node(last, _, _);
    //@ assert v0 == append(v1, v);
    
    //@ lseg2_lseg_to_lseg(f, n, last, v1, v);
    //@ assert lseg(f, last, v0);
    
    free(i);
    
    //@ close [f1]llist(l, v0);
    //@ close [f1 + f2]llist(l, v0);
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
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*& lseg(_n, n2, ?t