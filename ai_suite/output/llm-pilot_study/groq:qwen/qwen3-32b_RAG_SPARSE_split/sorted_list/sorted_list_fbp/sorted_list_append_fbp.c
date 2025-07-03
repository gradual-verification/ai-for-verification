#include <stdlib.h>
#include <limits.h>

struct node {
    int value;
    struct node *next;
};

/*@
predicate sorted_list(struct node *n, int lower, int upper) =
    n == 0 ?
        lower <= upper
    :
        malloc_block_node(n) &*&
        n->value |-> ?v &*& lower <= v &*& v <= upper &*&
        n->next |-> ?next &*& sorted_list(next, v, upper);
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
        return new_node;
    } else {
        head->next = append(head->next, value);
        return head;
    }
}