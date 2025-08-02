#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

/*@
// Define a predicate for a sorted list
predicate sorted_list(struct node *n; list<int> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        sorted_list(next, ?tail_values) &*&
        values == cons(v, tail_values) &*&
        (tail_values == nil || v <= head(tail_values));
@*/

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
    //@ close sorted_list(0, nil);
    return 0;
}