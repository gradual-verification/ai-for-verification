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
// Define a predicate for a linked list segment from 'from' to 'to' with a list of values
predicate lseg(struct node *from, struct node *to; list<int> values) =
  from == to ?
    values == nil
  :
    from != 0 &*& 
    from->value |-> ?v &*& 
    from->next |-> ?next &*& 
    malloc_block_node(from) &*& 
    lseg(next, to, ?tail) &*& 
    values == cons(v, tail);

// Define a predicate for the linked list structure
predicate llist(struct llist *list; list<int> values) =
  list->first |-> ?first &*& 
  list->last |-> ?last &*& 
  malloc_block_llist(list) &*& 
  lseg(first, 0, values) &*&
  (first == 0 ? last == 0 : true);

// Lemma to get the value at a specific index in a list
lemma int get_nth(list<int> values, int index);
  requires 0 <= index && index < length(values);
  ensures result == nth(index, values);
{
  switch(values) {
    case nil: return 0;
    case cons(h, t):
      if (index == 0) {
        return h;
      } else {
        return get_nth(t, index - 1);
      }
  }
}

// Lemma to split a list segment at a specific index
lemma void lseg_split(struct node *from, int index);
  requires lseg(from, 0, ?values) &*& 0 <= index &*& index < length(values);
  ensures lseg(from, ?mid, take(index, values)) &*& 
          mid != 0 &*& 
          mid->value |-> nth(index, values) &*& 
          mid->next |-> ?next &*& 
          malloc_block_node(mid) &*& 
          lseg(next, 0, drop(index + 1, values));
{
  open lseg(from, 0, values);
  if (index == 0) {
    close lseg(from, from, nil);
  } else {
    lseg_split(from->next, index - 1);
    close lseg(from, mid, take(index, values));
  }
}

// Lemma to join split list segments
lemma void lseg_join(struct node *from, struct node *mid);
  requires lseg(from, mid, ?prefix) &*& 
           mid != 0 &*& 
           mid->value |-> ?v &*& 
           mid->next |-> ?next &*& 
           malloc_block_node(mid) &*& 
           lseg(next, 0, ?suffix);
  ensures lseg(from, 0, append(prefix, cons(v, suffix)));
{
  open lseg(from, mid, prefix);
  if (from == mid) {
    close lseg(from, 0, cons(v, suffix));
  } else {
    lseg_join(from->next, mid);
    close lseg(from, 0, append(prefix, cons(v, suffix)));
  }
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `llist_lookup` function looks up the value at the given index in the linked list.
Note that the index in the linked list starts at 0.

@param list - Pointer to the linked list structure.
@param index - The index of the value to be looked up, which is within the range of the linked list.
@return - The value at the given index in the linked list.

It makes sure that the list is not changed, and the return value is the value at the given index in the list.
*/
/*@
// Specification for llist_lookup
requires llist(list, ?values) &*& 0 <= index &*& index < length(values);
ensures llist(list, values) &*& result == nth(index, values);
@*/
int llist_lookup(struct llist *list, int index)
{
  //@ open llist(list, values);
  struct node *f = list->first;
  struct node *l = list->last;
  //@ lseg_split(f, index);
  struct node *n = f;
  int i = 0;
  //@ close lseg(n, n, nil);
  while (i < index)
    /*@ invariant 0 <= i &*& i <= index &*& 
                  lseg(f, n, take(i, values)) &*& 
                  n != 0 &*& 
                  lseg(n, 0, drop(i, values)); @*/
  {
    //@ open lseg(n, 0, drop(i, values));
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ close lseg(n, n, nil);
  }
  //@ open lseg(n, 0, drop(i, values));
  int value = n->value;
  //@ assert value == nth(index, values);
  //@ close lseg(n->next, 0, drop(index + 1, values));
  //@ close lseg(n, 0, drop(index, values));
  //@ lseg_join(f, n);
  //@ close llist(list, values);
  return value;
}