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
predicate nodes(struct node *n, list<int> vs) =
    n == 0 ? 
        vs == nil 
    : 
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate llist(struct llist *l, list<int> vs) =
    l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*& nodes(first, vs);

predicate iter(struct iter *i, struct llist *l, list<int> vs) =
    i->current |-> ?current &*& malloc_block_iter(i) &*& llist(l, vs) &*& nodes(current, ?vs0) &*& mem(current, vs0) == true;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `iter_next` function returns the value of the current node of the iterator
and moves the iterator to the next node. It requires that the iterator is not at the end of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param i - Iterator of the linked list.
@return - The value of the original node that the iterator is at.
*/
int iter_next(struct iter *i)
    //@ requires iter(i, ?l, ?vs) &*& vs != nil;
    //@ ensures iter(i, l, tail(vs)) &*& result == head(vs);
{
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    return value;
}