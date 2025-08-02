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
// Define a predicate for a linked list node
predicate node(struct node *n, struct node *next, int value) =
    n->next |-> next &*& n->value |-> value &*& malloc_block_node(n);

// Define a predicate for a linked list segment
predicate lseg(struct node *from, struct node *to; list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        node(from, ?next, ?v) &*&
        lseg(next, to, ?tail) &*&
        values == cons(v, tail);

// Define a predicate for the linked list structure
predicate llist(struct llist *l, list<int> values) =
    l->first |-> ?first &*& l->last |-> ?last &*&
    lseg(first, 0, values) &*&
    malloc_block_llist(l);

// Define a predicate for the iterator
predicate iter(struct iter *i, struct llist *l, struct node *current) =
    i->current |-> current &*&
    malloc_block_iter(i);

// Define a predicate for a list with an iterator
predicate llist_with_iter(struct llist *l, struct iter *i, list<int> values) =
    l->first |-> ?first &*& l->last |-> ?last &*&
    i->current |-> ?current &*&
    lseg(first, 0, values) &*&
    malloc_block_llist(l) &*&
    malloc_block_iter(i) &*&
    (current == 0 || mem(current, nodes_of_lseg(first, 0)) == true);

// Helper fixpoint to get the list of nodes in a linked list segment
fixpoint list<struct node *> nodes_of_lseg(struct node *from, struct node *to) {
    return from == to ? nil : cons(from, nodes_of_lseg(from->next, to));
}
@*/

// TODO: make this function pass the verification
/**
 * Description:
The `llist_create_iter` function creates an iterator for a given linked list,
which is located at the first node of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param l - Pointer to the linked list structure.
@return - The created iterator pointing to the first node of linked list.
*/
struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l, ?values);
//@ ensures llist_with_iter(l, result, values);
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    //@ open llist(l, values);
    f = l->first;
    i->current = f;
    //@ close iter(i, l, f);
    //@ close llist_with_iter(l, i, values);
    return i;
}