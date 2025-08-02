#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

/*@
// Predicate to represent a sorted list with bounds
predicate sorted_list(struct node *head, int min, int max) =
    head == 0 ?
        true
    :
        head->value |-> ?v &*& 
        head->next |-> ?next &*& 
        malloc_block_node(head) &*&
        min <= v &*& v <= max &*&
        sorted_list(next, v, max);
@*/

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
// Specification for append function
requires sorted_list(head, ?min, ?max) &*& min <= value &*& value <= max;
ensures sorted_list(result, min, max);
@*/
struct node *append(struct node *head, int value)
{
    if (head == 0 || value <= head->value) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next = head;
        //@ close sorted_list(new_node, min, max);
        return new_node;
    } else {
        //@ open sorted_list(head, min, max);
        head->next = append(head->next, value);
        //@ close sorted_list(head, min, max);
        return head;
    }
}