#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

/*@
// Predicate for an ascendingly sorted list of integers.
predicate sorted_list(struct node *l; list<int> vs) =
    // An empty list is represented by a null pointer.
    l == 0 ?
        vs == nil
    :
        // A non-empty list points to a node...
        l->value |-> ?v &*&
        l->next |-> ?next &*&
        malloc_block_node(l) &*&
        // ...and the rest of the list is also a sorted list.
        sorted_list(next, ?tail) &*&
        // The sortedness invariant: current value is <= the next value.
        (tail == nil ? true : v <= head(tail)) &*&
        // The list of values is built recursively.
        vs == cons(v, tail);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_list` function creates an empty list. 
 *
 * The function ensures that the returned value is a sorted list. 
 */
struct node *create_list()
    //@ requires true;
    //@ ensures sorted_list(result, nil);
{
    return 0;
}