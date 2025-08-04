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

// TODO: make this function pass the verification
struct node *append(struct node *head, int value)
    //@ requires sorted_list(head, ?lower, ?upper) &*& lower <= value &*& value <= upper;
    //@ ensures sorted_list(result, lower, upper);
{
    if (head == 0 || value <= head->value) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next = head;
        //@ if (head == 0) open sorted_list(head, lower, upper);
        //@ close sorted_list(head, value, upper);
        //@ close sorted_list(new_node, lower, upper);
        return new_node;
    } else {
        // In this branch, head != 0 and value > head->value.
        // VeriFast opens sorted_list to evaluate the condition.
        head->next = append(head->next, value);
        //@ close sorted_list(head, lower, upper);
        return head;
    }
}