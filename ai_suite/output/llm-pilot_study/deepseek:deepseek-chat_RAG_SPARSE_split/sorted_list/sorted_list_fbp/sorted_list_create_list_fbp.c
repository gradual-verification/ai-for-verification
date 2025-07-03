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

struct node *create_list()
    //@ requires true;
    //@ ensures sorted_list(result, INT_MIN, INT_MAX);
{
    //@ close sorted_list(0, INT_MIN, INT_MAX);
    return 0;
}

/*@
lemma void sorted_list_limits(struct node *n, int lower, int upper)
    requires sorted_list(n, lower, upper);
    ensures sorted_list(n, lower, upper) &*& lower <= upper;
{
    open sorted_list(n, lower, upper);
    if (n != 0) {
        sorted_list_limits(n->next, n->value, upper);
    }
    close sorted_list(n, lower, upper);
}
@*/