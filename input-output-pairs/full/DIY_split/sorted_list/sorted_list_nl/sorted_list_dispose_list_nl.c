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
 * The `dispose_list` function disposes an sorted list. 
 * 
 * @param head: the head of a sorted list
 *
 * The function ensures that the list of head is freed. 
 */
void dispose_list(struct node *head)
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    }
}