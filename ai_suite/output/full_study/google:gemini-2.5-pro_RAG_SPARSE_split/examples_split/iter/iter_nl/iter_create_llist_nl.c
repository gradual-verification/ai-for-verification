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

predicate lseg_with_last(struct node *from, struct node *to, struct node *last, list<int> values) =
    from == to ?
        values == nil &*& last == 0
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?value &*&
        malloc_block_node(from) &*&
        (
            next == to ?
                // This is the last node of the segment.
                values == cons(value, nil) &*& last == from
            :
                // There are more nodes after this one.
                lseg_with_last(next, to, last, ?rest) &*& values == cons(value, rest)
        );

predicate llist(struct llist *l, list<int> values) =
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    malloc_block_llist(l) &*&
    lseg_with_last(first, 0, last, values);

@*/


// TODO: make this function pass the verification
/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
    //@ requires true;
    //@ ensures llist(result, cons(0, nil));
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close lseg_with_last(n, 0, n, cons(0, nil));
  //@ close llist(l, cons(0, nil));
  return l;
}