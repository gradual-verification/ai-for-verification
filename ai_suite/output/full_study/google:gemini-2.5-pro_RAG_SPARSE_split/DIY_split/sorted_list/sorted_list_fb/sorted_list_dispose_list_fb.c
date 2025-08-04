#include <stdlib.h>
#include <limits.h>

struct node {
    int value;
    struct node *next;
};

/*@
// A predicate for a malloc'd block for a single node.
// This is needed to be able to free the node.
predicate malloc_block_node(struct node *n) =
    malloc_block(n, sizeof(struct node));

predicate sorted_list(struct node *n, int lower_bound, int upper_bound) =
    n == 0 ?
        lower_bound <= upper_bound
    :
        malloc_block_node(n) &*&
        n->value |-> ?v &*& lower_bound <= v &*& v <= upper_bound &*&
        n->next |-> ?next &*& sorted_list(next, v, upper_bound);
@*/

// TODO: make this function pass the verification
void dispose_list(struct node *head)
    //@ requires sorted_list(head, ?lower, ?upper);
    //@ ensures true;
{
    //@ open sorted_list(head, lower, upper);
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    }
}