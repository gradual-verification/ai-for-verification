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
        n->value |-> ?v &*& lower_bound <= v &*& v <= upper_bound &*&
        n->next |-> ?next &*& sorted_list(next, v, upper_bound);
@*/

// TODO: make this function pass the verification
void dispose_list(struct node *head)
    //@ requires sorted_list(head, ?lower, ?upper);
    //@ ensures true;
{
    if (head != 0) {
        //@ open sorted_list(head, lower, upper);
        dispose_list(head->next);
        free(head);
    } else {
        //@ open sorted_list(head, lower, upper);
    }
}