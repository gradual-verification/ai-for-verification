#include <stdlib.h>
#include <limits.h>

struct node {
    int value;
    struct node *next;
};

/*@
predicate sorted_list(struct node *n, int lower_bound, int upper_bound) =
    n == 0 ?
        lower_bound <= upper_bound
    :
        malloc_block_node(n) &*&
        n->value |-> ?v &*& lower_bound <= v &*& v <= upper_bound &*&
        n->next |-> ?next &*& sorted_list(next, v, upper_bound);
@*/

// Verified implementation: returns an empty (and therefore trivially sorted) list
struct node *create_list()
    //@ requires true;
    //@ ensures sorted_list(result, INT_MIN, INT_MAX);
{
    //@ close sorted_list(0, INT_MIN, INT_MAX);   // INT_MIN <= INT_MAX holds
    return 0;
}