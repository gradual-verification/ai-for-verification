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
void dispose_list(struct node *head)
    //@ requires sorted_list(head, ?lower, ?upper);
    //@ ensures true;
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    }
}

/*@
lemma void dispose_list_lemma(struct node *head)
    requires sorted_list(head, ?lower, ?upper);
    ensures true;
{
    dispose_list(head);
}
@*/

// The main function to demonstrate the usage of dispose_list
int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *head = malloc(sizeof(struct node));
    if (head == 0) { abort(); }
    head->value = 10;
    head->next = malloc(sizeof(struct node));
    if (head->next == 0) { abort(); }
    head->next->value = 20;
    head->next->next = 0;

    // Ensure the list is sorted
    //@ close sorted_list(head, INT_MIN, INT_MAX);
    dispose_list(head);
    return 0;
}