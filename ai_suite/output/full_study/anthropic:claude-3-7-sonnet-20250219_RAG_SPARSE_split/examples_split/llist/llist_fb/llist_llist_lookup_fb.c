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

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  
  /*@
  // Initialize loop invariant
  if (f == l) {
    // Special case: list with only one element
    open lseg(f, l, _v);
    open node(l, _, _);
    close node(l, _, _);
    close lseg(f, l, _v);
  }
  @*/
  
  //@ assert lseg(f, l, _v);
  
  while (i < index)
    /*@ invariant 0 <= i &*& i <= index &*& 
                 lseg(f, l, _v) &*& node(l, _, _) &*&
                 n != 0 &*& lseg(f, n, ?prefix) &*& lseg(n, l, ?suffix) &*&
                 _v == append(prefix, suffix) &*& 
                 length(prefix) == i; @*/
  {
    //@ open lseg(n, l, suffix);
    struct node *next = n->next;
    n = next;
    i = i + 1;
    /*@
    // Update the invariant
    if (n == l) {
      // We've reached the last node
      assert lseg(f, n, ?new_prefix);
      assert length(new_prefix) == i;
      assert suffix == cons(?last_val, nil);
    }
    @*/
  }
  
  //@ open lseg(n, l, ?remaining);
  //@ assert n != 0;
  //@ open node(n, ?next_node, ?value);
  int value = n->value;
  //@ close node(n, next_node, value);
  //@ close lseg(n, l, remaining);
  
  /*@
  // Prove that value == nth(index, _v)
  assert length(prefix) == index;
  assert _v == append(prefix, suffix);
  assert suffix == cons(value, ?rest);
  nth_append(prefix, suffix, index);
  @*/
  
  //@ close llist(list, _v);
  return value;
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
// Helper lemma to relate nth and take/drop
lemma void nth_via_take_drop(list<int> vs, int index)
  requires 0 <= index && index < length(vs);
  ensures nth(index, vs) == head(drop(index, vs));
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if (index == 0) {
      } else {
        nth_via_take_drop(t, index - 1);
      }
  }
}

// Helper lemma to relate lseg and take/drop
lemma void lseg_split(struct node *from, struct node *to, int index)
  requires lseg(from, to, ?vs) &*& 0 <= index &*& index <= length(vs);
  ensures lseg(from, ?mid, take(index, vs)) &*& lseg(mid, to, drop(index, vs));
{
  open lseg(from, to, vs);
  if (from == to) {
    close lseg(from, from, nil);
    close lseg(from, to, nil);
  } else if (index == 0) {
    close lseg(from, from, nil);
    close lseg(from, to, vs);
  } else {
    lseg_split(from->next, to, index - 1);
    close lseg(from, mid, take(index, vs));
  }
}

// Helper lemma to merge two lsegs
lemma void lseg_join(struct node *from, struct node *mid, struct node *to)
  requires lseg(from, mid, ?vs1) &*& lseg(mid, to, ?vs2);
  ensures lseg(from, to, append(vs1, vs2));
{
  open lseg(from, mid, vs1);
  if (from == mid) {
    // Base case
  } else {
    lseg_join(from->next, mid, to);
    close lseg(from, to, append(vs1, vs2));
  }
}
@*/

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  
  //@ lseg_split(f, l, 0);
  //@ close lseg(f, f, nil);
  
  while (i < index)
    /*@ invariant 0 <= i &*& i <= index &*& 
                 lseg(f, n, take(i, _v)) &*& 
                 lseg(n, l, drop(i, _v)) &*& 
                 node(l, _, _); @*/
  {
    //@ open lseg(n, l, drop(i, _v));
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ lseg_join(f, n, l);
    //@ lseg_split(f, l, i);
  }
  
  //@ open lseg(n, l, drop(i, _v));
  //@ open node(n, ?next_node, ?value);
  int value = n->value;
  //@ close node(n, next_node, value);
  //@ close lseg(n, l, drop(i, _v));
  
  //@ lseg_join(f, n, l);
  //@ nth_via_take_drop(_v, index);
  //@ assert value == nth(index, _v);
  
  //@ close llist(list, _v);
  return value;
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

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  
  /*@
  // Define a ghost variable to track the list
  list<int> values = _v;
  @*/
  
  while (i < index)
    //@ invariant 0 <= i &*& i <= index &*& n != 0 &*& lseg(f, l, _v) &*& node(l, _, _) &*& values == _v;
  {
    //@ open lseg(f, l, _v);
    //@ if (f == n) { open node(n, _, _); }
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ close lseg(f, l, _v);
  }
  
  /*@
  // Use a lemma to prove that n points to the node at position 'index'
  lemma void get_nth_node(struct node *start, struct node *end, int pos)
    requires lseg(start, end, ?vs) &*& 0 <= pos &*& pos < length(vs);
    ensures lseg(start, end, vs) &*& nth(pos, vs) == ?val &*& 
            exists<struct node *>(?node) &*& node(node, _, val);
  {
    open lseg(start, end, vs);
    if (pos == 0) {
      close lseg(start, end, vs);
    } else {
      get_nth_node(start->next, end, pos - 1);
      close lseg(start, end, vs);
    }
  }
  
  get_nth_node(f, l, index);
  @*/
  
  int value = n->value;
  
  //@ close llist(list, _v);
  return value;
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

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?_v) &*& 0 <= index &*& index < length(_v);
  //@ ensures llist(list, _v) &*& result == nth(index, _v);
{
  //@ open llist(list, _v);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  
  /*@
  lemma void lseg_get_nth(struct node *from, struct node *to, int idx)
    requires lseg(from, to, ?vs) &*& 0 <= idx &*& idx < length(vs);
    ensures lseg(from, to, vs) &*& nth(idx, vs) == ?val &*& 
            exists<struct node *>(?n) &*& exists<struct node *>(?next) &*& 
            n->value |-> val &*& n->next |-> next;
  {
    open lseg(from, to, vs);
    if (idx == 0) {
      close exists<struct node *>(from->next);
      close exists<struct node *>(from);
      close lseg(from, to, vs);
    } else {
      lseg_get_nth(from->next, to, idx - 1);
      close lseg(from, to, vs);
    }
  }
  @*/
  
  while (i < index)
    //@ invariant 0 <= i &*& i <= index &*& lseg(f, l, _v) &*& node(l, _, _) &*& n != 0;
  {
    //@ open lseg(f, l, _v);
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ close lseg(f, l, _v);
  }
  
  //@ lseg_get_nth(f, l, index);
  //@ open node(n, ?next, ?val);
  int value = n->value;
  //@ close node(n, next, val);
  
  //@ close llist(list, _v);
  return value;
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
  n1 == n2 ? true &*& v == nil : node(n1, ?_n, ?h) &*&