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

struct node *append(struct node *head, int value)
    //@ requires sorted_list(head, ?lower, ?upper) &*& lower <= value &*& value <= upper;
    //@ ensures sorted_list(result, lower, upper);
{
    if (head == 0 || value <= head->value) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
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

/*@
lemma void sorted_list_append_lemma(struct node *head, int value)
    requires sorted_list(head, ?lower, ?upper) &*& lower <= value &*& value <= upper;
    ensures sorted_list(head, lower, upper);
{
    open sorted_list(head, lower, upper);
    if (head != 0) {
        if (value > head->value) {
            sorted_list_append_lemma(head->next, value);
        }
        close sorted_list(head, lower, upper);
    } else {
        close sorted_list(0, lower, upper);
    }
}
@*/