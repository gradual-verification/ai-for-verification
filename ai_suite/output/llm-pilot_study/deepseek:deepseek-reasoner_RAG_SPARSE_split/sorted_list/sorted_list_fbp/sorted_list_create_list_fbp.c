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

// Verified implementation
struct node *create_list()
    //@ requires true;
    //@ ensures sorted_list(result, INT_MIN, INT_MAX);
{
    int dummy = 0; // Dummy variable for proof
    //@ close integer(&dummy, 0); // Create integer chunk
    //@ integer_limits(&dummy); // Derive INT_MIN <= 0 and 0 <= INT_MAX
    //@ close sorted_list(0, INT_MIN, INT_MAX); // Close predicate using derived bounds
    return 0;
}