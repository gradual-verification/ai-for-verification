#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
// Define a predicate for a linked list segment
predicate lseg(struct node *from, struct node *to; list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?value &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?tail_values) &*&
        values == cons(value, tail_values);

// Define a predicate for the linked list
predicate llist(struct llist *list; list<int> values) =
    list->first |-> ?first &*&
    list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    lseg(first, 0, values) &*&
    (first == 0 ? last == 0 : last != 0);

// Define a predicate for an iterator
predicate iter(struct iter *i, struct llist *list; struct node *current, list<int> values) =
    i->current |-> current &*&
    malloc_block_iter(i) &*&
    lseg(current, 0, values);
@*/

/***
 * Description:
The `iter_next` function returns the value of the current node of the iterator
and moves the iterator to the next node. It requires that the iterator is not at the end of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param i - Iterator of the linked list.
@return - The value of the original node that the iterator is at.
*/
int iter_next(struct iter *i)
//@ requires iter(i, ?list, ?current, ?values) &*& current != 0;
//@ ensures iter(i, list, ?next, ?tail_values) &*& values == cons(result, tail_values);
{
    //@ open iter(i, list, current, values);
    struct node *c = i->current;
    //@ open lseg(c, 0, values);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close lseg(n, 0, ?tail_values);
    //@ close iter(i, list, n, tail_values);
    return value;
}