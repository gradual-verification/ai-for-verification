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
        return new_node;
    } else {
        struct node *next = append(head->next, value);
        head->next = next;
        return head;
    }
}

/*@
lemma void append_sorted_list(struct node *head, int value, int lower, int upper)
    requires sorted_list(head, lower, upper) &*& lower <= value &*& value <= upper;
    ensures sorted_list(append(head, value), lower, upper);
{
    if (head == 0 || value <= head->value) {
        // Base case: inserting at the head
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next = head;
        // We need to show that the new list is sorted
        // Since head is sorted and new_node is less than or equal to head->value
        // The new list is sorted
        sorted_list(new_node, lower, upper);
    } else {
        // Recursive case: we need to append to the tail
        append_sorted_list(head->next, value, head->value, upper);
        // After the recursive call, we need to ensure that the head remains sorted
        // The head's value is still less than the next node's value
        sorted_list(head, lower, upper);
    }
}
@*/