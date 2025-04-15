#include <stdlib.h>
#include <limits.h>

struct node {
    int value;
    struct node *next;
};

/***
 * Description:
 * The `create_list` function creates an empty list. 
 *
 * The function ensures that the returned value trivially has the sorted list property. 
 */
struct node *create_list()
{
    return 0;
}

/***
 * Description:
 * The `append` function appends a node of given value to a sorted list, and still keeps the list sorted. 
 *
 * @param head: the head of a given sorted list, which has the sorted list property
 * @param val: the given value to be added. It is within the bound of the nax and min value of the sorted list. 
 * 
 * The function inserts the value at the proper position of the list.
 * It makes sure that the new list is still sorted. 
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

/***
 * Description:
 * The `dispose_list` function disposes an sorted list. 
 * 
 * @param head: the head of a sorted list
 *
 * The function ensures that the list is freed. 
 */
void dispose_list(struct node *head)
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    }
}