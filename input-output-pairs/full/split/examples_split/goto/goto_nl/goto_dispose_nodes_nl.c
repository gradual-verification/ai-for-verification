#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The dispose_nodes function iteratively frees the nodes of a given linked list, by using a loop with a goto.

@param head: pointing to the head of the given linked list

It makes sure that the nodes in the linked list are freed. 
*/
void dispose_nodes(struct node *head)
{
loop:
    if (head == 0) return;
    struct node *next = head->next;
    free(head);
    head = next;
    goto loop;
}

