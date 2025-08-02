#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

/*@
// Define a predicate for a sorted list
predicate sorted_list(struct node *head; list<int> values) =
    head == 0 ?
        values == nil
    :
        head->value |-> ?v &*& 
        head->next |-> ?next &*& 
        malloc_block_node(head) &*&
        sorted_list(next, ?tail_values) &*&
        values == cons(v, tail_values) &*&
        (tail_values == nil || v <= head(tail_values));
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_list` function disposes an sorted list. 
 * 
 * @param head: the head of a sorted list
 *
 * The function ensures that the list of head is freed. 
 */
/*@
// Lemma to help with verification
lemma void sorted_list_to_unsorted(struct node *head)
    requires sorted_list(head, ?values);
    ensures head == 0 ? true : 
            head->value |-> ?v &*& 
            head->next |-> ?next &*& 
            malloc_block_node(head) &*&
            sorted_list(next, ?tail_values);
{
    open sorted_list(head, values);
}
@*/

void dispose_list(struct node *head)
//@ requires sorted_list(head, ?values);
//@ ensures true;
{
    if (head != 0) {
        //@ sorted_list_to_unsorted(head);
        dispose_list(head->next);
        free(head);
    }
    //@ else open sorted_list(head, _);
}