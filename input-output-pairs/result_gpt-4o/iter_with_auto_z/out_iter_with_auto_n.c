#include "stdlib.h"

/*@
predicate node(struct node *n, struct node *next, int value) =
    n != 0 && n->next |-> next &*& n->value |-> value;

predicate llist(struct llist *l, struct node *first, struct node *last) =
    l != 0 && l->first |-> first &*& l->last |-> last;

predicate nodes(struct node *first, struct node *last) =
    first == last ? emp : node(first, ?next, _) &*& nodes(next, last);

predicate llist(struct llist *l) =
    l != 0 && l->first |-> ?first &*& l->last |-> ?last &*& nodes(first, last);
@*/

/**
 * Description:
 * The `create_llist` function dynamically allocates memory for a linked list structure
 * and initializes it with an empty node (where first = last).
 *
 * @return - Pointer to the newly created linked list structure.
 */
/*@
requires true;
ensures result != 0 &*& llist(result);
@*/
struct llist *create_llist() {
    struct llist *l = malloc(sizeof(struct llist));
    if (l == 0) abort();

    struct node *n = calloc(1, sizeof(struct node));
    if (n == 0) abort();

    l->first = n;
    l->last = n;

    //@ close nodes(n, n);
    //@ close llist(l);

    return l;
}
