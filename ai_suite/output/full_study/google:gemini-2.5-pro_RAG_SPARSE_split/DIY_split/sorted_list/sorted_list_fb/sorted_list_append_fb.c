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
struct node *append(struct node *head, int value)
    //@ requires sorted_list(head, ?lower, ?upper) &*& lower <= value &*& value <= upper;
    //@ ensures sorted_list(result, lower, upper);
{
    //@ open sorted_list(head, lower, upper);
    if (head == 0 || value <= head->value) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next = head;
        if (head == 0) {
            // Case: The original list was empty.
            // The new list is just the new node.
            // We need to show that sorted_list(0, value, upper) holds.
            // This requires 'value <= upper', which is true by the function's precondition.
            //@ close sorted_list(0, value, upper);
        } else {
            // Case: The new value is the smallest.
            // The new node is inserted at the front.
            // We need to show that sorted_list(head, value, upper) holds.
            // This requires 'value <= head->value', which is true by the 'if' condition.
            //@ close sorted_list(head, value, upper);
        }
        //@ close sorted_list(new_node, lower, upper);
        return new_node;
    } else {
        // Case: The insertion point is further down the list.
        // We recursively call append on the rest of the list.
        // The precondition for the recursive call holds because:
        // 1. head->next is a sorted_list with lower bound head->value.
        // 2. value > head->value, so 'value' is within the new lower bound.
        // 3. 'value <= upper' is from the original precondition.
        struct node *new_next = append(head->next, value);
        head->next = new_next;
        //@ close sorted_list(head, lower, upper);
        return head;
    }
}