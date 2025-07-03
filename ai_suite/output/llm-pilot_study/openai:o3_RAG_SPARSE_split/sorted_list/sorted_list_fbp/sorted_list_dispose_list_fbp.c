#include <stdlib.h>
#include <limits.h>

struct node {
    int value;
    struct node *next;
};

/*@
predicate sorted_list(struct node *n, int lower_bound, int upper_bound) =
    n == 0 ?
        lower_bound <= upper_bound                                        // no memory to free
    :
        malloc_block_node(n) &*&                                          // memory owned
        n->value |-> ?v &*& lower_bound <= v &*& v <= upper_bound &*&     // ordered element
        n->next |-> ?next &*& sorted_list(next, v, upper_bound);          // tail is also sorted
@*/

/*  Recursively frees a list satisfying ‘sorted_list’.
    After the call no heap chunks remain. */
void dispose_list(struct node *head)
    //@ requires sorted_list(head, ?lower, ?upper);
    //@ ensures true;
{
    //@ open sorted_list(head, lower, upper);
    if (head != 0) {
        dispose_list(head->next);   // recursively dispose the tail
        free(head);                 // free the node opened above
    }
}