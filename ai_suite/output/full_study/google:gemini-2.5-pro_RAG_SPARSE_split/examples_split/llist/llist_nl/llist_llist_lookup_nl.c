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

// A predicate for a segment of a linked list from 'from' to 'to'.
// 'values' is a ghost list representing the integer values in the nodes.
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?rest) &*&
        values == cons(v, rest);

// A predicate for the complete linked list structure.
predicate llist(struct llist *l, list<int> values) =
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    malloc_block_llist(l) &*&
    lseg(first, 0, values) &*&
    // A simple property for the last pointer. Not strictly needed for lookup.
    (values == nil ? last == 0 : true);

// Lemma to extend a list segment with one node.
// This is used in the loop to "move" a node from the remaining part to the traversed part.
lemma void lseg_extend(struct node *from, struct node *to)
    requires lseg(from, to, ?vs) &*&
             to != 0 &*&
             to->value |-> ?v &*&
             to->next |-> ?next &*&
             malloc_block_node(to) &*&
             lseg(next, 0, ?vs_end);
    ensures lseg(from, next, append(vs, cons(v, nil))) &*& lseg(next, 0, vs_end);
{
    open lseg(from, to, vs);
    if (from == to) {
        // Base case: the segment to extend is empty.
        // We can close lseg(next, next, nil) from emp.
        close lseg(next, next, nil);
        close lseg(from, next, cons(v, nil));
    } else {
        // Recursive step: extend the tail of the segment.
        lseg_extend(from->next, to);
        close lseg(from, next, append(vs, cons(v, nil)));
    }
}

// Lemma to merge two adjacent list segments.
// This is used after the loop to restore the single lseg predicate for the whole list.
lemma void lseg_merge(struct node *n1, struct node *n2)
    requires lseg(n1, n2, ?vs1) &*& lseg(n2, 0, ?vs2);
    ensures lseg(n1, 0, append(vs1, vs2));
{
    open lseg(n1, n2, vs1);
    if (n1 != n2) {
        lseg_merge(n1->next, n2);
    }
    close lseg(n1, 0, append(vs1, vs2));
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
int llist_lookup(struct llist *list, int index)
    //@ requires llist(list, ?values) &*& 0 <= index &*& index < length(values);
    //@ ensures llist(list, values) &*& result == nth(index, values);
{
  //@ open llist(list, values);
  struct node *f = list->first;
  struct node *l = list->last;
  //@ assert lseg(f, 0, values);
  struct node *n = f;
  int i = 0;
  //@ close lseg(f, f, nil); // Establish the invariant for the first time.
  while (i < index)
    /*@
    invariant
        list->first |-> f &*& list->last |-> l &*& malloc_block_llist(list) &*&
        0 <= i &*& i <= index &*&
        lseg(f, n, take(i, values)) &*&
        lseg(n, 0, drop(i, values));
    @*/
  {
    //@ open lseg(n, 0, drop(i, values));
    struct node *next = n->next;
    //@ lseg_extend(f, n);
    n = next;
    i = i + 1;
  }
  
  //@ assert i == index;
  //@ assert lseg(n, 0, drop(index, values));
  //@ open lseg(n, 0, drop(index, values));
  int value = n->value;
  //@ assert value == nth(index, values);
  
  //@ close lseg(n, 0, drop(index, values));
  //@ lseg_merge(f, n);
  //@ append_take_drop_n(values, index);
  //@ close llist(list, values);
  return value;
}