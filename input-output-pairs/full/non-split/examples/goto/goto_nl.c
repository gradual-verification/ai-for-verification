#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

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

/***
 * Description:
The nested_blocks function tests whether the goto statement can get out of the while loop,
and it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function

It makes sure that nodes n1 and n2 are not modified.
*/
void nested_blocks(struct node *n1, struct node *n2)
{
    while (true)
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
}

/***
 * Description:
The break_test function tests whether the break statement can get out of the while loop,
and it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function

It makes sure that n1 and n2 are unchanged. 
*/
void break_test(struct node *n1, struct node *n2)
{
    while (true)
    {
        break;
    }
}
