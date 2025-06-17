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
struct node *create_list()
    //@ requires true;
    //@ ensures sorted_list(result, INT_MIN, INT_MAX);
{
    return 0;
}

// TODO: make this function pass the verification
struct node *append(struct node *head, int value)
    //@ requires sorted_list(head, ?lower, ?upper) &*& lower <= value &*& value <= upper;
    //@ ensures sorted_list(result, lower, upper);
{
    if (head == 0 || value <= head->value) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        //@ open sorted_list(head, lower, upper);
        new_node->value = value;
        new_node->next = head;
        //@ close sorted_list(new_node, lower, upper);
        return new_node;
    } else {
        //@ open sorted_list(head, lower, upper);
        head->next = append(head->next, value);
        //@ close sorted_list(head, lower, upper);
        return head;
    }
}

// TODO: make this function pass the verification
void dispose_list(struct node *head)
    //@ requires sorted_list(head, ?lower, ?upper);
    //@ ensures true;
{
    if (head != 0) {
        //@ open sorted_list(head, lower, upper);
        dispose_list(head->next);
        free(head);
    }
}