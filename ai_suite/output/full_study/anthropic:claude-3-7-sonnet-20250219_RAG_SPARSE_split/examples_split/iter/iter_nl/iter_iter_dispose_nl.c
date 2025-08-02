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
// Predicate for a node in the linked list
predicate node(struct node *n; int value) =
    n->value |-> value &*& n->next |-> _ &*& malloc_block_node(n);

// Predicate for an iterator
predicate iter(struct iter *i; struct node *current) =
    i->current |-> current &*& malloc_block_iter(i);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `iter_dispose` function deallocates the memory associated with the iterator.

@param i - Iterator of the linked list
*/
void iter_dispose(struct iter *i)
    //@ requires iter(i, ?current);
    //@ ensures emp;
{
    //@ open iter(i, current);
    free(i);
}