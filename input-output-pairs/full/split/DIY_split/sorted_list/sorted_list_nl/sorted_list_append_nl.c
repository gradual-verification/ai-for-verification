#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

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
struct node *append(struct node *head, int value)
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
