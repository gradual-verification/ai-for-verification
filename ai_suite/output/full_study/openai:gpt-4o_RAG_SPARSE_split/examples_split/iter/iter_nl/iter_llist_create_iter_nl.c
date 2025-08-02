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
predicate nodes(struct node *n; list<int> vs) =
    n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate llist(struct llist *l; list<int> vs) =
    l->first |-> ?f &*& l->last |-> ?last &*& malloc_block_llist(l) &*& nodes(f, vs);

predicate iter(struct iter *i, struct llist *l; list<int> vs) =
    i->current |-> ?c &*& malloc_block_iter(i) &*& nodes(c, ?vs0) &*& llist(l, vs) &*& (vs0 == vs || mem(head(vs0), vs) == true);
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
    //@ requires llist(l, ?vs);
    //@ ensures iter(result, l, vs);
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    f = l->first;
    i->current = f;
    //@ close iter(i, l, vs);
    return i;
}