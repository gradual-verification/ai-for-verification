#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
// A predicate for a linked list of nodes.
// It models the list's structure as a ghost list of `unit`s,
// since the nodes themselves do not store any data.
predicate list(struct node *n; list<unit> vs) =
    n == 0 ?
        vs == nil
    :
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        list(next, ?tail_vs) &*&
        vs == cons(unit, tail_vs);
@*/

/***
 * Description:
 * The `create_list` function creates an empty list.
 *
 * It makes sure that the return value is the head of a list. 
 */
struct node *create_list()
    //@ requires true;
    //@ ensures list(result, nil);
{
    return 0;
}