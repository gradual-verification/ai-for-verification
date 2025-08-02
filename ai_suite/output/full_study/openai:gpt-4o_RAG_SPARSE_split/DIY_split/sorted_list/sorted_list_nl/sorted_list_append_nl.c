#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

/*@
predicate sorted_list(struct node *node, int min, int max, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->value |-> ?value &*& node->next |-> ?next &*& malloc_block_node(node) &*&
        min <= value &*& value <= max &*&
        sorted_list(next, value, max, ?next_values) &*&
        values == cons(value, next_values) &*&
        (next == 0 ? true : value <= head(next_values));
@*/

/*@
lemma void sorted_list_append_lemma(struct node *node, int value)
    requires sorted_list(node, ?min, ?max, ?values) &*& min <= value &*& value <= max;
    ensures sorted_list(node, min, max, append(values, cons(value, nil)));
{
    open sorted_list(node, min, max, values);
    if (node != 0) {
        sorted_list_append_lemma(node->next, value);
    }
    close sorted_list(node, min, max, append(values, cons(value, nil)));
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `append` function appends a node of given value to a sorted list, and still keeps the list sorted. 
 *
 * @param head: the head of a given sorted list
 * @param val: the given value to be added. It is within the bound of the max and min value of the sorted list. 
 * 
 * It makes sure that the new list is still sorted with the same bound of max and min value. 
 */
/*@
requires sorted_list(head, ?min, ?max, ?values) &*& min <= value &*& value <= max;
ensures sorted_list(result, min, max, append(values, cons(value, nil)));
@*/
struct node *append(struct node *head, int value)
{
    if (head == 0 || value <= head->value) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next = head;
        //@ close sorted_list(new_node, min, max, cons(value, values));
        return new_node;
    } else {
        //@ open sorted_list(head, min, max, values);
        head->next = append(head->next, value);
        //@ close sorted_list(head, min, max, append(values, cons(value, nil)));
        return head;
    }
}