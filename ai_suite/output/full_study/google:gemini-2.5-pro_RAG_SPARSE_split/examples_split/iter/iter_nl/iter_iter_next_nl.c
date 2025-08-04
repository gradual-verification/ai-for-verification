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
// A predicate for a single node.
// It represents ownership of the node's fields and its memory block.
predicate node_pred(struct node *n, int v, struct node *next) =
    n->value |-> v &*&
    n->next |-> next &*&
    malloc_block_node(n);

// A predicate for an iterator.
// It represents ownership of the iterator struct's fields and its memory block.
// 'current' is the node the iterator currently points to.
predicate iter_pred(struct iter *i, struct node *current) =
    i->current |-> current &*&
    malloc_block_iter(i);
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
    //@ requires iter_pred(i, ?c) &*& c != 0 &*& [?f]node_pred(c, ?v, ?n);
    //@ ensures iter_pred(i, n) &*& [f]node_pred(c, v, n) &*& result == v;
{
    //@ open iter_pred(i, c);
    //@ open [f]node_pred(c, v, n);
    struct node *current_node = i->current;
    int value = current_node->value;
    struct node *next_node = current_node->next;
    i->current = next_node;
    //@ close [f]node_pred(c, v, n);
    //@ close iter_pred(i, n);
    return value;
}